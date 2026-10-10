# Data Lakehouse Gateway: Formal Model (TLA+ / PlusCal)

A formal specification of the coordination protocol of a distributed lakehouse query gateway, model-checked with [TLC](https://github.com/tlaplus/tlaplus).

The model covers multi-tenant admission, async job leasing with epoch fencing, claim-check result storage, a result cache, snapshot invalidation, garbage collection and fault recovery. It exists to find concurrency and isolation bugs in the design before they reach code.

> **Status:** the spec has not yet been run through the PlusCal translator or TLC. Translate and check it before relying on any result. See [Known limitations](#known-limitations).

## Repository layout

```
data-lakehouse-gateway-formal/
├── README.md
├── .gitignore
├── spec/                          # TLC resolves modules from one directory, so these stay together
│   ├── DataLakehouseGateway.tla   # The design: PlusCal algorithm, invariants, properties
│   ├── MC.tla                     # Model-checking module: concrete scenario
│   ├── MC.cfg                     # Baseline run: bounds, switches, properties to check
│   ├── MC_nofaults.cfg            # No crashes or timeouts (fast first pass)
│   ├── MC_mutant.cfg              # Injects the tenant bug (expected to FAIL)
│   ├── MC_lowblobs.cfg            # Blob pool pressure
│   └── MC_flightcache.cfg         # Flight results enter the shared cache
├── scripts/
│   ├── translate.sh               # PlusCal -> TLA+
│   ├── check.sh                   # Run TLC on one config
│   └── run_all.sh                 # Run all scenarios and compare with expected outcomes
├── docs/
│   └── model-validation-section.html   # Blog-ready write-up of what is verified and the gaps found
└── tools/
    └── README.md                  # Put tla2tools.jar here (git-ignored)
```

| Path | Role |
|---|---|
| `spec/DataLakehouseGateway.tla` | The only file describing the system. Constants, shared definitions, the PlusCal algorithm (variables, `define` block of invariants and properties, processes), and the generated TLA+ translation. |
| `spec/MC.tla` | Extends the spec, declares model values, and builds the per-request lookup tables that a `.cfg` cannot express directly. |
| `spec/*.cfg` | Bind constants, set fault and snapshot bounds, and list the `INVARIANTS` and `PROPERTIES` TLC checks. Each variant is the baseline with one change. |
| `scripts/` | Thin wrappers around the translator and TLC. Set `TLA_JAR` to use a jar outside `tools/`. |
| `docs/` | Documentation for publishing. |

## Prerequisites

- Java 11 or newer
- `tla2tools.jar` from the [TLA+ releases page](https://github.com/tlaplus/tlaplus/releases), placed in `tools/` (or pointed to with `TLA_JAR`)

## Quick start

```bash
# 1. Translate PlusCal to TLA+ (rewrites the .tla in place, keeps a .old backup)
scripts/translate.sh

# 2. Model-check the baseline scenario
scripts/check.sh            # same as: scripts/check.sh MC.cfg

# 3. Or run any variant, or everything
scripts/check.sh MC_mutant.cfg
scripts/run_all.sh
```

Re-run step 1 after every edit to the algorithm. Never hand-edit the region between `\* BEGIN TRANSLATION` and `\* END TRANSLATION`.

For a fast first pass use `MC_nofaults.cfg`, or add `-simulate` to the TLC command in `scripts/check.sh`. Simulation mode does not check liveness, so use full runs for `PROPERTIES`.

## The model

### Processes

| Process | Models |
|---|---|
| `ClientProcess` (per request) | Admission, tenant check, snapshot binding, cache lookup, Flight or REST routing, result release |
| `ComputeWorker` | Claim, execute, stage blob, publish pointer, commit, populate cache |
| `LeaseManager` | Expires leases of dead owners, and (bounded) of live workers (zombies) |
| `GarbageCollector` | Reclaims released, unreferenced and orphaned staged blobs |
| `CacheEvictor` | TTL/LRU abstraction so the cache cannot pin the blob pool forever |
| `LakehouseETL` | Advances tenant snapshots and invalidates stale cache entries |
| `Crasher` / `Recoverer` | Bounded worker crashes and recovery (after leases are reaped) |

### Design decisions encoded

- **Flight is in-VM.** Flight requests are admitted and executed inside the same VM, so no network boundary is crossed for data transfer. The Flight path therefore has no queue, lease, epoch fence or crash window. It is one atomic local step. A VM crash is a dropped client connection, and the client retries. By default Flight results are not written to the shared cache.
- **Two-phase result write.** Workers write a staged blob that records its writer and lease epoch, then publish the pointer under a fenced compare-and-set. A fenced-out worker leaves an orphan the GC reclaims.
- **Snapshot isolation at admission.** A request is bound to the tenant's snapshot at admission and may legitimately return that older version.
- **Cache is best-effort.** Never assume a cache entry exists after a job completes.

## What is checked

### Safety invariants (`INVARIANTS`)

| Group | Properties |
|---|---|
| Type | `TypeOK` |
| Tenant isolation and authorization | `TenantBinding`, `RLSEnforcement`, `UnauthorizedIsInert`, `MismatchRejected`, `TenantIsolation` |
| Result, blob and cache integrity | `DeliveredResultIntegrity`, `ClaimCheckIntegrity`, `BlobPtrIffResultState`, `NoSharedBlobPointer`, `BlobPoolConsistency`, `StagedBlobWellFormed`, `CacheIntegrity`, `CacheFreshness` |
| Job, lease and queue | `ExactlyOnceCommit`, `FailedImpliesExhausted`, `LeaseOwnership`, `QueueConsistency`, `FlightIsLocal`, `SnapshotBound` |

### Transition properties (`PROPERTIES`)

`EpochMonotonic`, `SnapshotNeverChanges`, `CatalogMonotonic`, `TerminalAbsorbing`, `CommitMonotonic`, `DeliveryImmutable`

### Liveness (`PROPERTIES`)

`LiveTermination`, `ClientsComplete`, `GCReclaimsGarbage`

Liveness holds under weak fairness of the GC, lease manager, evictor, ETL, recoverer, workers and clients, with crashes and timeouts bounded.

## Configuration

### Constants

| Constant | Meaning |
|---|---|
| `Tenants`, `Clients`, `Requests`, `Queries`, `Workers`, `Blobs` | Model-value sets |
| `MaxSnapshot` | Number of catalog snapshots per tenant |
| `MaxAttempts` | Retry budget per REST job |
| `MaxCrashes` | Fail-stop worker crash budget |
| `MaxTimeouts` | Lease timeouts on live workers (zombie budget) |
| `RequestedTenantOf`, `AuthenticatedTenantOf`, `QueryOf`, `ClientOf`, `ProtocolOf`, `SecurityContextOf` | Per-request functions, supplied by `MC.tla` |
| `FlightPopulatesCache` | Whether Flight results enter the shared cache (default `FALSE`) |
| `MutantSkipTenantCheck` | Injects the "trust the payload tenant" bug (default `FALSE`) |

### Baseline scenario (`MC.cfg`)

| Parameter | Value |
|---|---|
| Tenants | `{t1, t2}` |
| Requests | `r1` Flight, `r2` REST, `r3` REST with a different security context, `r4` REST with a tenant mismatch |
| Workers / Blobs | 2 / 4 |
| `MaxSnapshot` / `MaxAttempts` | 2 / 2 |
| `MaxCrashes` / `MaxTimeouts` | 1 / 1 |

`CHECK_DEADLOCK FALSE` is set because the background processes idle forever when the system is quiet. Stuck work is caught by the liveness properties instead.

### Suggested scenario variants

These configs ship in `spec/`; each is `MC.cfg` with one change:

| Config | Change | Expectation |
|---|---|---|
| `MC_nofaults.cfg` | `MaxCrashes = 0`, `MaxTimeouts = 0` | Clean, fast first pass |
| `MC_mutant.cfg` | `MutantSkipTenantCheck = TRUE` | **Should fail**, proving the tenant invariants can detect the bug |
| `MC_lowblobs.cfg` | `Blobs = {b1, b2}` | Stresses the pool; liveness depends on GC and evictor progress |
| `MC_flightcache.cfg` | `FlightPopulatesCache = TRUE` | Exercises the Flight to cache path |

Run a variant with `scripts/check.sh <config>`; `scripts/run_all.sh` runs them all and flags unexpected outcomes.

## Interpreting results

- **No violation** means no counterexample exists within the configured bounds. This is bounded model checking, not a proof for unbounded sizes.
- **A violation** comes with a step-by-step counterexample trace. Treat a failure in the baseline as a real finding. Only the mutant run is expected to fail.
- Keep the `Requests` and `Workers` sets disjoint, and keep the string process IDs (`"LeaseManager"`, and so on) distinct from them.

## Assumptions

- The authenticated tenant and security context come from a trusted verifier such as a signed JWT. The payload tenant is untrusted, and contexts do not change during a request.
- The job store supports atomic compare-and-set on state, owner and lease epoch. Every fence in the model depends on this.
- Published result blobs are immutable, and publication is atomic.
- Faults are fail-stop crashes and bounded lease timeouts only. No Byzantine behavior, clock skew, message loss or duplicate queue delivery.
- The task queue is a reliable FIFO.
- A replacement worker starts only after the crashed worker's leases are reclaimed.
- Snapshots are per-tenant integers, queries are opaque IDs, and cache identity is an exact match on tenant, query, snapshot and security context. Row-level security is modeled as a flag set at execution time. The model does not check the SQL rewriting itself.

## Design gaps found during analysis

Static review of the first model revisions produced the requirements below.

| # | Gap | Requirement |
|---|---|---|
| 1 | Cache invalidation on snapshot commit was off by one | Invalidate every entry at or below the old snapshot atomically with the advance |
| 2 | Delivered blobs were never reclaimed | Define result lifetime with a client release or TTL |
| 3 | Tenant-mismatch check compared pre-step placeholder values (dead code) | Compare trusted and untrusted tenants directly at the admission boundary |
| 4 | Unconditional lease expiry made liveness hold vacuously | Expire only on owner death or heartbeat timeout; FAILED only after retries are exhausted |
| 5 | Cache key did not include the security context | Include the security context in the key |
| 6 | Blob write and pointer publish were one atomic step | Stage the blob, then publish under a fenced compare-and-set |
| 7 | GC could not distinguish in-flight from orphaned blobs | Reclaim a staged blob only once the lease epoch has moved past the blob's epoch |
| 8 | Cache population races with client release and GC | Re-verify the blob atomically on insert, or use a conditional put |
| 9 | Cache entries pin blobs with no eviction | Add TTL or LRU eviction and a pool-pressure policy |
| 10 | A crashed worker could return before its leases were reclaimed | Reclaim leases first, or give workers an incarnation number |
| 11 | Commit and cache write were a single step | Treat the cache as best-effort |
| 12 | Freshness contract was unstated | Document snapshot isolation at admission |
| 13 | Flight has no fencing or recovery by design | State that Flight failure means client retry |

Gap 3 rests on my understanding of PlusCal evaluating right-hand sides in the pre-step state. Confirm it in the translated TLA+.

## Known limitations

- **Not yet executed.** The spec has not been translated or checked. Expect to fix translator or TLC errors on the first run.
- **Bounded.** Results apply only to the configured sizes.
- **Out of scope for this iteration:**
  - Permission revocation and policy-version changes
  - Snapshot expiry while a job is bound
  - Single-flight coalescing of identical queries
  - Real clock-based TTLs and heartbeats
  - VM-level crashes on the Flight path

## Contributing changes to the model

1. Edit the algorithm in `DataLakehouseGateway.tla`, and keep definitions used by variable initializers above the algorithm.
2. Avoid reading a variable after assigning it in the same PlusCal step. Reads see the pre-step value.
3. Add or update the matching invariant or property, and list it in `MC.cfg`.
4. Re-run the translator, then the baseline and the mutant configs.

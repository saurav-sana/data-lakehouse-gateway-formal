---------------------- MODULE DataLakehouseGateway ----------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* DATA LAKEHOUSE GATEWAY - PATCHED ARCHITECTURE MODEL (v2)                *)
(*                                                                         *)
(* NOT YET RUN THROUGH THE PLUSCAL TRANSLATOR OR TLC. Translate and check  *)
(* before relying on it.                                                   *)
(*                                                                         *)
(* CHANGES vs v1                                                           *)
(*  1. ETL cache invalidation off-by-one fixed (old snapshot is now        *)
(*     invalidated in the same step the catalog advances).                 *)
(*  2. Blob lifecycle: STAGED -> PUBLISHED -> RELEASED -> reclaimed by GC. *)
(*     Clients release results; GC reclaims released, evicted, or          *)
(*     fenced-out (orphaned) blobs. v1 never freed a delivered blob.       *)
(*  3. Blob write split into AllocateBlob / PublishPointer so a zombie     *)
(*     worker can orphan a blob (models real claim-check behaviour).       *)
(*  4. Commit split into CommitJob / PopulateCache (cache write is         *)
(*     best-effort and separately crashable).                              *)
(*  5. Lease expiry is conditional: owner dead, or a bounded number of     *)
(*     "timeout" expiries (zombie workers). Recovery of a worker waits     *)
(*     until its leases are reaped.                                        *)
(*  6. Cache key now really includes the security context.                 *)
(*  7. RLS predicate is applied at execution time, not at job creation.    *)
(*  8. Reads of variables assigned earlier in the same step were removed   *)
(*     (PlusCal evaluates right-hand sides in the pre-step state).         *)
(*  9. Cache evictor (TTL/LRU abstraction) added so the cache cannot pin   *)
(*     the blob pool forever.                                              *)
(* 10. Flight path documented as a deliberate in-VM design (see below).    *)
(* 11. Mutation switch MutantSkipTenantCheck to prove the tenant           *)
(*     invariants can actually fail.                                       *)
(*                                                                         *)
(* FLIGHT DESIGN DECISION (intentional asymmetry)                          *)
(*   FLIGHT requests are admitted and executed inside the same VM, so no   *)
(*   network boundary is crossed for data transfer. Therefore the Flight   *)
(*   path has no queue, no lease, no epoch fence, no RUNNING state and no  *)
(*   worker crash window: it is one atomic local step. A VM crash is       *)
(*   observed by the client as a dropped connection (client retries as a   *)
(*   new request) and is outside this model. By default Flight results     *)
(*   are not written to the shared result cache (FlightPopulatesCache).    *)
(***************************************************************************)

CONSTANTS
    Tenants, Clients, Requests, Queries, Workers, Blobs,
    MaxSnapshot, MaxAttempts, MaxCrashes, MaxTimeouts,
    RequestedTenantOf,        \* untrusted tenant from caller payload
    AuthenticatedTenantOf,    \* tenant from verified auth (e.g. JWT)
    QueryOf, ClientOf,
    ProtocolOf,               \* "FLIGHT" (sync, in-VM) or "REST" (async)
    SecurityContextOf,
    FlightPopulatesCache,     \* BOOLEAN: should Flight results enter cache?
    MutantSkipTenantCheck     \* BOOLEAN: FALSE normally; TRUE = inject bug

ASSUME
    /\ DOMAIN RequestedTenantOf = Requests
    /\ DOMAIN AuthenticatedTenantOf = Requests
    /\ DOMAIN QueryOf = Requests
    /\ DOMAIN ClientOf = Requests
    /\ DOMAIN ProtocolOf = Requests
    /\ DOMAIN SecurityContextOf = Requests
    /\ \A r \in Requests :
        /\ RequestedTenantOf[r] \in Tenants
        /\ AuthenticatedTenantOf[r] \in Tenants
        /\ QueryOf[r] \in Queries
        /\ ClientOf[r] \in Clients
        /\ ProtocolOf[r] \in {"FLIGHT", "REST"}
    /\ MaxSnapshot >= 1 /\ MaxAttempts >= 1
    /\ MaxCrashes \in Nat /\ MaxTimeouts \in Nat
    /\ FlightPopulatesCache \in BOOLEAN
    /\ MutantSkipTenantCheck \in BOOLEAN
    /\ Requests \cap Workers = {}

NONE == "NONE"

SecCtxs == {SecurityContextOf[r] : r \in Requests}

NoEntry == [valid |-> FALSE, blob_id |-> NONE]

FreeBlob == [allocated        |-> FALSE,
             staged           |-> FALSE,   \* written by a worker, not yet published
             req              |-> NONE,    \* staging request (if staged)
             epoch            |-> 0,       \* staging lease epoch (if staged)
             tenant           |-> NONE,
             query            |-> NONE,
             version          |-> 0,
             security_context |-> NONE]


(*--algorithm DataLakehouseGateway

variables
    \* Independently advancing Iceberg snapshot per tenant.
    catalog_snapshot = [t \in Tenants |-> 1],

    \* Result cache. Key = tenant, query, snapshot, security context.
    cache = [t \in Tenants |-> [q \in Queries |-> [v \in 1..MaxSnapshot |->
                [s \in SecCtxs |-> NoEntry]]]],

    \* Async REST queue.
    task_queue = << >>,

    jobs = [r \in Requests |->
            [state                     |-> "IDLE",
             owner                     |-> NONE,
             lease_epoch               |-> 0,
             attempts                  |-> 0,
             requested_tenant          |-> RequestedTenantOf[r],
             tenant                    |-> NONE,
             query                     |-> QueryOf[r],
             security_context          |-> NONE,
             version                   |-> 0,
             blob_ptr                  |-> NONE,
             protocol                  |-> ProtocolOf[r],
             rls_applied               |-> FALSE,
             executed_predicate_tenant |-> NONE]],

    \* Claim-check object storage (immutable result blobs).
    blob_storage = [b \in Blobs |-> FreeBlob],
    available_blobs = Blobs,

    worker_alive = [w \in Workers |-> TRUE],

    client_received = [r \in Requests |->
                        [delivered        |-> FALSE,
                         released         |-> FALSE,  \* client finished / dropped result
                         blob_id          |-> NONE,
                         tenant           |-> NONE,
                         query            |-> NONE,
                         version          |-> 0,
                         security_context |-> NONE]],

    commit_count = [r \in Requests |-> 0],

    crashes  = 0,    \* fault budget: worker crashes
    timeouts = 0;    \* fault budget: lease timeouts on live workers (zombies)

define
    Pending   == {"QUEUED", "CLAIMED", "RUNNING", "RESULT_WRITTEN"}
    Active    == {"CLAIMED", "RUNNING", "RESULT_WRITTEN"}
    Terminal  == {"COMPLETED", "FAILED", "UNAUTHORIZED"}
    AllStates == {"IDLE"} \cup Pending \cup Terminal

    \* Tenant the gateway actually uses. The mutant uses the untrusted one.
    EffTenant(r) == IF MutantSkipTenantCheck
                    THEN RequestedTenantOf[r]
                    ELSE AuthenticatedTenantOf[r]

    HoldsLease(r, e, w, st) ==
        /\ jobs[r].lease_epoch = e
        /\ jobs[r].owner = w
        /\ jobs[r].state = st

    QCount(r) == Cardinality({i \in 1..Len(task_queue) : task_queue[i] = r})

    BlobMatches(b, t, q, v, s) ==
        /\ blob_storage[b].tenant = t
        /\ blob_storage[b].query = q
        /\ blob_storage[b].version = v
        /\ blob_storage[b].security_context = s

    BlobCached(b) ==
        \E t \in Tenants, q \in Queries, v \in 1..MaxSnapshot, s \in SecCtxs :
            cache[t][q][v][s].valid /\ cache[t][q][v][s].blob_id = b

    BlobJobHeld(b) ==
        \E r \in Requests : jobs[r].blob_ptr = b /\ ~client_received[r].released

    BlobClientHeld(b) ==
        \E r \in Requests : client_received[r].delivered
                            /\ ~client_received[r].released
                            /\ client_received[r].blob_id = b

    \* A staged blob is garbage once its writer's lease epoch is superseded:
    \* the writer can never publish it (epoch fence).
    StagedOrphan(b) ==
        jobs[blob_storage[b].req].lease_epoch /= blob_storage[b].epoch

    GCable == {b \in Blobs :
                /\ blob_storage[b].allocated
                /\ IF blob_storage[b].staged
                   THEN StagedOrphan(b)
                   ELSE ~BlobCached(b) /\ ~BlobJobHeld(b) /\ ~BlobClientHeld(b)}

    ExpirableJobs == {r \in Requests :
                        /\ jobs[r].state \in Active
                        /\ (~worker_alive[jobs[r].owner] \/ timeouts < MaxTimeouts)}

    CachedKeys == {k \in Tenants \X Queries \X (1..MaxSnapshot) \X SecCtxs :
                        cache[k[1]][k[2]][k[3]][k[4]].valid}

    (***********************************************************************)
    (* A. TYPE INVARIANT                                                   *)
    (***********************************************************************)
    TypeOK ==
        /\ catalog_snapshot \in [Tenants -> 1..MaxSnapshot]
        /\ available_blobs \subseteq Blobs
        /\ worker_alive \in [Workers -> BOOLEAN]
        /\ crashes \in 0..MaxCrashes
        /\ timeouts \in 0..MaxTimeouts
        /\ task_queue \in Seq(Requests)
        /\ \A t \in Tenants, q \in Queries, v \in 1..MaxSnapshot, s \in SecCtxs :
              /\ cache[t][q][v][s].valid \in BOOLEAN
              /\ cache[t][q][v][s].blob_id \in Blobs \cup {NONE}
        /\ \A b \in Blobs :
              /\ blob_storage[b].allocated \in BOOLEAN
              /\ blob_storage[b].staged \in BOOLEAN
        /\ \A r \in Requests :
              /\ jobs[r].state \in AllStates
              /\ jobs[r].attempts \in 0..MaxAttempts
              /\ jobs[r].lease_epoch \in Nat
              /\ jobs[r].blob_ptr \in Blobs \cup {NONE}
              /\ commit_count[r] \in 0..1
              /\ client_received[r].delivered => client_received[r].blob_id /= NONE

    (***********************************************************************)
    (* B1. SAFETY - TENANT / AUTHORIZATION                                 *)
    (***********************************************************************)
    \* Every admitted job is bound to the authenticated tenant and context.
    TenantBinding ==
        \A r \in Requests :
            jobs[r].state \notin {"IDLE", "UNAUTHORIZED"} =>
                /\ jobs[r].tenant = AuthenticatedTenantOf[r]
                /\ jobs[r].security_context = SecurityContextOf[r]

    \* Row-level-security predicate is applied, with the right tenant, by the
    \* time a job is executing or has produced a result.
    RLSEnforcement ==
        \A r \in Requests :
            jobs[r].state \in {"RUNNING", "RESULT_WRITTEN", "COMPLETED"} =>
                /\ jobs[r].rls_applied
                /\ jobs[r].executed_predicate_tenant = AuthenticatedTenantOf[r]

    \* A rejected request leaves no trace: no work, no data, no queue entry.
    UnauthorizedIsInert ==
        \A r \in Requests :
            jobs[r].state = "UNAUTHORIZED" =>
                /\ jobs[r].blob_ptr = NONE
                /\ jobs[r].owner = NONE
                /\ jobs[r].attempts = 0
                /\ commit_count[r] = 0
                /\ ~client_received[r].delivered
                /\ QCount(r) = 0

    \* Mismatched requested/authenticated tenant is always rejected.
    MismatchRejected ==
        \A r \in Requests :
            RequestedTenantOf[r] /= AuthenticatedTenantOf[r] =>
                /\ jobs[r].state \in {"IDLE", "UNAUTHORIZED"}
                /\ ~client_received[r].delivered

    \* What a client receives belongs to its authenticated tenant.
    TenantIsolation ==
        \A r \in Requests :
            client_received[r].delivered =>
                /\ client_received[r].tenant = AuthenticatedTenantOf[r]
                /\ client_received[r].security_context = SecurityContextOf[r]
                /\ client_received[r].query = QueryOf[r]

    (***********************************************************************)
    (* B2. SAFETY - RESULT / BLOB / CACHE INTEGRITY                        *)
    (***********************************************************************)
    \* While the client still holds a result, the blob behind it is intact,
    \* published, and carries exactly the tenant/query/context/version.
    DeliveredResultIntegrity ==
        \A r \in Requests :
            (client_received[r].delivered /\ ~client_received[r].released) =>
                /\ blob_storage[client_received[r].blob_id].allocated
                /\ ~blob_storage[client_received[r].blob_id].staged
                /\ BlobMatches(client_received[r].blob_id,
                               AuthenticatedTenantOf[r], QueryOf[r],
                               client_received[r].version, SecurityContextOf[r])

    \* Claim-check pointer of an unreleased result is valid and matches job.
    ClaimCheckIntegrity ==
        \A r \in Requests :
            (jobs[r].state \in {"RESULT_WRITTEN", "COMPLETED"}
             /\ ~client_received[r].released) =>
                /\ blob_storage[jobs[r].blob_ptr].allocated
                /\ ~blob_storage[jobs[r].blob_ptr].staged
                /\ BlobMatches(jobs[r].blob_ptr, jobs[r].tenant, jobs[r].query,
                               jobs[r].version, jobs[r].security_context)

    BlobPtrIffResultState ==
        \A r \in Requests :
            (jobs[r].blob_ptr /= NONE) <=>
                (jobs[r].state \in {"RESULT_WRITTEN", "COMPLETED"})

    NoSharedBlobPointer ==
        \A r1, r2 \in Requests :
            (r1 /= r2 /\ jobs[r1].blob_ptr /= NONE /\ jobs[r2].blob_ptr /= NONE
             /\ ~client_received[r1].released /\ ~client_received[r2].released) =>
                jobs[r1].blob_ptr /= jobs[r2].blob_ptr

    BlobPoolConsistency ==
        available_blobs = {b \in Blobs : ~blob_storage[b].allocated}

    StagedBlobWellFormed ==
        \A b \in Blobs :
            blob_storage[b].staged =>
                /\ blob_storage[b].allocated
                /\ blob_storage[b].req \in Requests
                /\ jobs[blob_storage[b].req].lease_epoch >= blob_storage[b].epoch

    \* A valid cache entry points at an intact published blob for ITS key.
    CacheIntegrity ==
        \A t \in Tenants, q \in Queries, v \in 1..MaxSnapshot, s \in SecCtxs :
            cache[t][q][v][s].valid =>
                /\ blob_storage[cache[t][q][v][s].blob_id].allocated
                /\ ~blob_storage[cache[t][q][v][s].blob_id].staged
                /\ BlobMatches(cache[t][q][v][s].blob_id, t, q, v, s)

    \* Only the current snapshot's results may be cached.
    CacheFreshness ==
        \A t \in Tenants, q \in Queries, v \in 1..MaxSnapshot, s \in SecCtxs :
            cache[t][q][v][s].valid => v = catalog_snapshot[t]

    (***********************************************************************)
    (* B3. SAFETY - JOB / LEASE / QUEUE                                    *)
    (***********************************************************************)
    ExactlyOnceCommit ==
        \A r \in Requests :
            /\ commit_count[r] <= 1
            /\ (jobs[r].state = "COMPLETED") <=> (commit_count[r] = 1)

    \* A job fails only after every attempt was spent.
    FailedImpliesExhausted ==
        \A r \in Requests :
            jobs[r].state = "FAILED" => jobs[r].attempts = MaxAttempts

    LeaseOwnership ==
        \A r \in Requests :
            /\ jobs[r].state \in Active => jobs[r].owner \in Workers
            /\ jobs[r].state \notin Active => jobs[r].owner = NONE

    \* Queue holds a job exactly once iff it is QUEUED.
    QueueConsistency ==
        \A r \in Requests :
            /\ jobs[r].state = "QUEUED" => QCount(r) = 1
            /\ jobs[r].state /= "QUEUED" => QCount(r) = 0

    \* Flight is local: never queued, never leased, always one attempt.
    FlightIsLocal ==
        \A r \in Requests :
            ProtocolOf[r] = "FLIGHT" =>
                /\ jobs[r].state \in {"IDLE", "COMPLETED", "UNAUTHORIZED"}
                /\ jobs[r].owner = NONE
                /\ QCount(r) = 0

    SnapshotBound ==
        \A r \in Requests :
            /\ jobs[r].state \notin {"IDLE", "UNAUTHORIZED"} =>
                   jobs[r].version \in 1..catalog_snapshot[jobs[r].tenant]
            /\ client_received[r].delivered =>
                   client_received[r].version
                       \in 1..catalog_snapshot[AuthenticatedTenantOf[r]]

    (***********************************************************************)
    (* C. SAFETY - ACTION / TRANSITION PROPERTIES                          *)
    (***********************************************************************)
    EpochMonotonic ==
        [][\A r \in Requests : jobs'[r].lease_epoch >= jobs[r].lease_epoch]_vars

    SnapshotNeverChanges ==
        [][\A r \in Requests :
              (jobs[r].state /= "IDLE" /\ jobs'[r].state /= "IDLE") =>
                  jobs'[r].version = jobs[r].version]_vars

    CatalogMonotonic ==
        [][\A t \in Tenants : catalog_snapshot'[t] >= catalog_snapshot[t]]_vars

    TerminalAbsorbing ==
        [][\A r \in Requests :
              jobs[r].state \in Terminal => jobs'[r].state = jobs[r].state]_vars

    CommitMonotonic ==
        [][\A r \in Requests : commit_count'[r] >= commit_count[r]]_vars

    DeliveryImmutable ==
        [][\A r \in Requests :
              client_received[r].delivered =>
                  /\ client_received'[r].delivered
                  /\ client_received'[r].blob_id = client_received[r].blob_id
                  /\ client_received'[r].version = client_received[r].version]_vars

    (***********************************************************************)
    (* D. LIVENESS                                                         *)
    (***********************************************************************)
    LiveTermination ==
        \A r \in Requests :
            (jobs[r].state \in Pending) ~> (jobs[r].state \in Terminal)

    ClientsComplete ==
        \A r \in Requests : <>(client_received[r].released)

    GCReclaimsGarbage ==
        \A b \in Blobs : (b \in GCable) ~> (b \notin GCable)
end define;


(***************************************************************************)
(* CLIENT / GATEWAY FRONT END                                              *)
(***************************************************************************)
fair process ClientProcess \in Requests
variables req_version = 0;
begin
Start:
    \* Security boundary: reject mismatched requested vs authenticated tenant.
    \* Uses the constants directly (no read-after-write inside the step).
    if ~MutantSkipTenantCheck
       /\ AuthenticatedTenantOf[self] /= RequestedTenantOf[self] then
        jobs[self] := [jobs[self] EXCEPT !.state = "UNAUTHORIZED"];
        goto Release;
    end if;

BindSnapshot:
    req_version := catalog_snapshot[EffTenant(self)];

CheckCache:
    if cache[EffTenant(self)][QueryOf[self]][req_version][SecurityContextOf[self]].valid then
        client_received[self] :=
            [client_received[self] EXCEPT
                !.delivered = TRUE,
                !.blob_id = cache[EffTenant(self)][QueryOf[self]][req_version][SecurityContextOf[self]].blob_id,
                !.tenant = EffTenant(self),
                !.query = QueryOf[self],
                !.version = req_version,
                !.security_context = SecurityContextOf[self]];
        goto Release;
    end if;

InitializeJob:
    jobs[self] := [jobs[self] EXCEPT
        !.tenant = EffTenant(self),
        !.security_context = SecurityContextOf[self],
        !.version = req_version];

Route:
    if ProtocolOf[self] = "FLIGHT" then
        goto ExecuteFlight;
    else
        goto EnqueueREST;
    end if;

ExecuteFlight:
    \* In-VM synchronous execution: no network hop, no queue, no lease.
    \* Allocation, RLS-filtered execution, publication and delivery are one
    \* local step by design.
    await available_blobs /= {};
    with b \in available_blobs do
        available_blobs := available_blobs \ {b};
        blob_storage[b] := [FreeBlob EXCEPT
            !.allocated = TRUE,
            !.tenant = jobs[self].tenant,
            !.query = jobs[self].query,
            !.version = jobs[self].version,
            !.security_context = jobs[self].security_context];
        jobs[self] := [jobs[self] EXCEPT
            !.state = "COMPLETED",
            !.lease_epoch = 1,
            !.attempts = 1,
            !.blob_ptr = b,
            !.rls_applied = TRUE,
            !.executed_predicate_tenant = jobs[self].tenant];
        commit_count[self] := commit_count[self] + 1;
        client_received[self] := [client_received[self] EXCEPT
            !.delivered = TRUE,
            !.blob_id = b,
            !.tenant = jobs[self].tenant,
            !.query = jobs[self].query,
            !.version = jobs[self].version,
            !.security_context = jobs[self].security_context];
        if FlightPopulatesCache
           /\ jobs[self].version = catalog_snapshot[jobs[self].tenant] then
            cache[jobs[self].tenant][jobs[self].query][jobs[self].version][jobs[self].security_context] :=
                [valid |-> TRUE, blob_id |-> b];
        end if;
    end with;
    goto Release;

EnqueueREST:
    jobs[self] := [jobs[self] EXCEPT !.state = "QUEUED", !.attempts = @ + 1];
    task_queue := Append(task_queue, self);

AwaitREST:
    await jobs[self].state \in Terminal;
    if jobs[self].state = "COMPLETED" then
        client_received[self] := [client_received[self] EXCEPT
            !.delivered = TRUE,
            !.blob_id = jobs[self].blob_ptr,
            !.tenant = jobs[self].tenant,
            !.query = jobs[self].query,
            !.version = jobs[self].version,
            !.security_context = jobs[self].security_context];
    end if;

Release:
    \* Client has consumed (or abandoned) the result. Blob becomes reclaimable
    \* once the cache and job no longer reference it either.
    client_received[self] := [client_received[self] EXCEPT !.released = TRUE];
end process;


(***************************************************************************)
(* REST COMPUTE WORKER                                                     *)
(***************************************************************************)
fair process ComputeWorker \in Workers
variables curr_req = NONE, curr_epoch = 0, curr_blob = NONE;
begin
ClaimTask:
    while TRUE do
        await Len(task_queue) > 0 /\ worker_alive[self];
        with r = Head(task_queue) do
            task_queue := Tail(task_queue);
            curr_req := r;
            curr_blob := NONE;
            if jobs[r].state = "QUEUED" then
                curr_epoch := jobs[r].lease_epoch + 1;
                jobs[r] := [jobs[r] EXCEPT
                    !.owner = self, !.state = "CLAIMED", !.lease_epoch = @ + 1];
            else
                curr_epoch := 0;
            end if;
        end with;

StartExecution:
        if curr_epoch > 0 /\ worker_alive[self]
           /\ HoldsLease(curr_req, curr_epoch, self, "CLAIMED") then
            \* RLS predicate is applied when execution starts.
            jobs[curr_req] := [jobs[curr_req] EXCEPT
                !.state = "RUNNING",
                !.rls_applied = TRUE,
                !.executed_predicate_tenant = jobs[curr_req].tenant];
        else
            goto ClaimTask;
        end if;

AllocateBlob:
        \* Wait for a free blob unless we crashed or lost the lease.
        await ~worker_alive[self]
              \/ ~HoldsLease(curr_req, curr_epoch, self, "RUNNING")
              \/ available_blobs /= {};
        if worker_alive[self]
           /\ HoldsLease(curr_req, curr_epoch, self, "RUNNING")
           /\ available_blobs /= {} then
            with b \in available_blobs do
                available_blobs := available_blobs \ {b};
                curr_blob := b;
                blob_storage[b] := [FreeBlob EXCEPT
                    !.allocated = TRUE,
                    !.staged = TRUE,
                    !.req = curr_req,
                    !.epoch = curr_epoch,
                    !.tenant = jobs[curr_req].tenant,
                    !.query = jobs[curr_req].query,
                    !.version = jobs[curr_req].version,
                    !.security_context = jobs[curr_req].security_context];
            end with;
        else
            goto ClaimTask;   \* a staged blob (if any) is left to the GC
        end if;

PublishPointer:
        if worker_alive[self]
           /\ HoldsLease(curr_req, curr_epoch, self, "RUNNING") then
            jobs[curr_req] := [jobs[curr_req] EXCEPT
                !.blob_ptr = curr_blob, !.state = "RESULT_WRITTEN"];
            blob_storage[curr_blob] := [blob_storage[curr_blob] EXCEPT !.staged = FALSE];
        else
            goto ClaimTask;   \* fenced: blob is an orphan, GC reclaims it
        end if;

CommitJob:
        if worker_alive[self]
           /\ HoldsLease(curr_req, curr_epoch, self, "RESULT_WRITTEN") then
            jobs[curr_req] := [jobs[curr_req] EXCEPT
                !.state = "COMPLETED", !.owner = NONE];
            commit_count[curr_req] := commit_count[curr_req] + 1;
        else
            goto ClaimTask;
        end if;

PopulateCache:
        \* Best effort and race-safe: only cache if this is still the current
        \* snapshot and the blob is still the intact published result.
        if worker_alive[self]
           /\ jobs[curr_req].state = "COMPLETED"
           /\ jobs[curr_req].blob_ptr = curr_blob
           /\ blob_storage[curr_blob].allocated
           /\ ~blob_storage[curr_blob].staged
           /\ BlobMatches(curr_blob, jobs[curr_req].tenant, jobs[curr_req].query,
                          jobs[curr_req].version, jobs[curr_req].security_context)
           /\ jobs[curr_req].version = catalog_snapshot[jobs[curr_req].tenant] then
            cache[jobs[curr_req].tenant][jobs[curr_req].query][jobs[curr_req].version][jobs[curr_req].security_context] :=
                [valid |-> TRUE, blob_id |-> curr_blob];
        end if;
    end while;
end process;


(***************************************************************************)
(* LEASE MANAGER                                                           *)
(* Expires a lease when the owner is dead, or (bounded) on timeout of a    *)
(* live worker, which creates zombie workers that the epoch fence stops.   *)
(* Blobs are NOT freed here; the GC reclaims them.                         *)
(***************************************************************************)
fair process LeaseManager = "LeaseManager"
begin
LeaseLoop:
    while TRUE do
        with r \in ExpirableJobs do
            \* Count a timeout when the owner is still alive (zombie worker).
            \* Placed before the jobs[r] update so the owner is read pre-step.
            if worker_alive[jobs[r].owner] then
                timeouts := timeouts + 1;
            end if;
            if jobs[r].attempts < MaxAttempts then
                jobs[r] := [jobs[r] EXCEPT
                    !.owner = NONE, !.state = "QUEUED",
                    !.attempts = @ + 1, !.lease_epoch = @ + 1,
                    !.blob_ptr = NONE, !.rls_applied = FALSE,
                    !.executed_predicate_tenant = NONE];
                task_queue := Append(task_queue, r);
            else
                jobs[r] := [jobs[r] EXCEPT
                    !.owner = NONE, !.state = "FAILED",
                    !.lease_epoch = @ + 1, !.blob_ptr = NONE,
                    !.rls_applied = FALSE,
                    !.executed_predicate_tenant = NONE];
            end if;
        end with;
    end while;
end process;


(***************************************************************************)
(* GARBAGE COLLECTOR                                                       *)
(* Reclaims (a) orphaned staged blobs whose writer is fenced out, and      *)
(* (b) published blobs referenced by no cache entry, live job or client.   *)
(***************************************************************************)
fair process GarbageCollector = "GarbageCollector"
begin
GCLoop:
    while TRUE do
        with b \in GCable do
            blob_storage[b] := FreeBlob;
            available_blobs := available_blobs \union {b};
        end with;
    end while;
end process;


(***************************************************************************)
(* CACHE EVICTOR (TTL / LRU abstraction)                                   *)
(***************************************************************************)
fair process CacheEvictor = "CacheEvictor"
begin
EvictLoop:
    while TRUE do
        with e \in CachedKeys do
            cache[e[1]][e[2]][e[3]][e[4]] := NoEntry;
        end with;
    end while;
end process;


(***************************************************************************)
(* CHAOS: WORKER CRASHES (bounded by MaxCrashes)                           *)
(***************************************************************************)
process Crasher = "Crasher"
begin
CrashLoop:
    while crashes < MaxCrashes do
        with w \in {x \in Workers : worker_alive[x]} do
            worker_alive[w] := FALSE;
            crashes := crashes + 1;
        end with;
    end while;
end process;


(***************************************************************************)
(* WORKER RECOVERY                                                         *)
(* A replacement comes up only after the dead worker's leases are reaped.  *)
(***************************************************************************)
fair process Recoverer = "Recoverer"
begin
RecoverLoop:
    while TRUE do
        with w \in {x \in Workers :
                      /\ ~worker_alive[x]
                      /\ \A r \in Requests :
                            ~(jobs[r].owner = x /\ jobs[r].state \in Active)} do
            worker_alive[w] := TRUE;
        end with;
    end while;
end process;


(***************************************************************************)
(* LAKEHOUSE ETL / SNAPSHOT COMMITS                                        *)
(***************************************************************************)
fair process LakehouseETL = "LakehouseETL"
begin
ETLCommit:
    while TRUE do
        with t \in {x \in Tenants : catalog_snapshot[x] < MaxSnapshot} do
            \* FIX: invalidate every version <= the OLD snapshot (i.e. < new).
            \* The cache is assigned before catalog_snapshot so both read the
            \* pre-step value regardless of evaluation order.
            cache[t] := [q \in Queries |-> [v \in 1..MaxSnapshot |-> [s \in SecCtxs |->
                IF v < catalog_snapshot[t] + 1
                THEN NoEntry
                ELSE cache[t][q][v][s]]]];
            catalog_snapshot[t] := catalog_snapshot[t] + 1;
        end with;
    end while;
end process;

end algorithm; *)

=============================================================================

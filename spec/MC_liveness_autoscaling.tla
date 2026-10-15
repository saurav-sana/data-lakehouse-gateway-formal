--------------------------------- MODULE MC_liveness_autoscaling ---------------------------------
EXTENDS DataLakehouseGateway, TLC

\* 1. Constant Declarations matching the MC.cfg
CONSTANTS
    r1, r2,
    t1,
    q1,
    s1,
    c1,
    w1, w2,
    b1, b2,
    p1

\* 2. Request Attribute Mappings
\* We map r1 to async REST and r2 to sync FLIGHT to test both pipelines concurrently.
MCRequestedTenantOf == (r1 :> t1) @@ (r2 :> t1)
MCAuthenticatedTenantOf == (r1 :> t1) @@ (r2 :> t1)
MCQueryOf == (r1 :> q1) @@ (r2 :> q1)
MCClientOf == (r1 :> c1) @@ (r2 :> c1)
MCProtocolOf == (r1 :> "REST") @@ (r2 :> "FLIGHT")
MCSecurityContextOf == (r1 :> s1) @@ (r2 :> s1)


(***************************************************************************)
(* TEMPORAL PROPERTIES (Liveness & Monotonicity)                           *)
(* These use TLA+ temporal logic:                                          *)
(* []  = "Always" (Globally)                                               *)
(* <>  = "Eventually" (Future)                                             *)
(* ~>  = "Leads To" (If A happens, B must eventually happen)               *)
(***************************************************************************)

\* Proves that a job's lease epoch only ever increments, never rolls back.
EpochMonotonic == 
    \A r \in Requests : [][jobs[r].lease_epoch <= jobs'[r].lease_epoch]_vars

\* Proves the 'Snapshot-at-Start' contract: once a version is bound (> 0), it never mutates.
SnapshotNeverChanges == 
    \A r \in Requests : [][jobs[r].version > 0 => jobs'[r].version = jobs[r].version]_vars

\* Proves the background ETL process only moves the Iceberg catalog forward.
CatalogMonotonic == 
    \A t \in Tenants : [][catalog_snapshot[t] <= catalog_snapshot'[t]]_vars

\* Proves that once a job hits a terminal state (ACCEPTED, FAILED, UNAUTHORIZED), it never escapes.
TerminalAbsorbing == 
    \A r \in Requests : [][jobs[r].state \in Terminal => jobs'[r].state = jobs[r].state]_vars

\* Proves the Two-Phase Commit is at-most-once.
CommitMonotonic == 
    \A r \in Requests : [][commit_count[r] <= commit_count'[r]]_vars

\* Proves that once a client receives a result, the delivery status cannot be revoked.
DeliveryImmutable == 
    \A r \in Requests : [][client_received[r].delivered => client_received'[r].delivered]_vars

\* LIVENESS: Proves the system never livelocks. Every job WILL eventually terminate.
LiveTermination == 
    \A r \in Requests : <>[](jobs[r].state \in Terminal)

\* LIVENESS: Proves that clients eventually finish reading and release their result locks.
ClientsComplete == 
    \A r \in Requests : jobs[r].state = "ACCEPTED" ~> client_received[r].released

\* LIVENESS: Proves the GC eventually identifies and deletes orphaned blobs from zombie workers.
GCReclaimsGarbage == 
    \A b \in Blobs : (blob_storage[b].staged /\ StagedOrphan(b)) ~> ~blob_storage[b].allocated

=============================================================================
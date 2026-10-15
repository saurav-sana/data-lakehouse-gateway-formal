--------------------------- MODULE MC_retry_exhaustion ---------------------------
EXTENDS DataLakehouseGateway, TLC

\* 1. Constant Declarations matching the MC.cfg
CONSTANTS
    r1,
    t1,
    q1,
    s1,
    c1,
    w1, w2,
    b1, b2,
    p1

(***************************************************************************)
(* REQUEST ATTRIBUTE MAPPINGS                                              *)
(* A stripped-down, single-request topology to isolate retry exhaustion.   *)
(* We route r1 through the REST path so it can be claimed by w1, forcibly  *)
(* timed out, retried by w2, timed out again, and permanently FAILED.      *)
(***************************************************************************)

MCRequestedTenantOf == (r1 :> t1)
MCAuthenticatedTenantOf == (r1 :> t1)
MCQueryOf == (r1 :> q1)
MCClientOf == (r1 :> c1)
MCProtocolOf == (r1 :> "REST")
MCSecurityContextOf == (r1 :> s1)

(***************************************************************************)
(* TEMPORAL PROPERTIES (Liveness & Resource Reclamation)                   *)
(***************************************************************************)

\* LIVENESS: Proves the system never livelocks. Every job eventually hits 
\* ACCEPTED, UNAUTHORIZED, CACHED, or FAILED.
LiveTermination == 
    \A r \in Requests : <>[](jobs[r].state \in Terminal)

\* LIVENESS: Proves the GC eventually identifies and deletes orphaned blobs, 
\* EVEN IF the parent job has permanently died in the FAILED state.
GCReclaimsGarbage == 
    \A b \in Blobs : (blob_storage[b].staged /\ StagedOrphan(b)) ~> ~blob_storage[b].allocated

=============================================================================
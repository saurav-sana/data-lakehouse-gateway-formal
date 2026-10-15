--------------------------------- MODULE MC_storage_starvation_contention ---------------------------------
EXTENDS DataLakehouseGateway, TLC

\* 1. Constant Declarations matching the MC.cfg
CONSTANTS
    r1, r2, r3,
    t1,
    q1,
    s1,
    c1,
    w1, w2,
    b1, b2,
    p1

(***************************************************************************)
(* REQUEST ATTRIBUTE MAPPINGS                                              *)
(* We deliberately route all 3 requests through the REST path to force     *)
(* maximum contention over the 2 available worker object blobs, proving    *)
(* the GC safely recycles blobs without deadlocking the compute queue.     *)
(***************************************************************************)

MCRequestedTenantOf == 
    (r1 :> t1) @@ (r2 :> t1) @@ (r3 :> t1)

MCAuthenticatedTenantOf == 
    (r1 :> t1) @@ (r2 :> t1) @@ (r3 :> t1)

MCQueryOf == 
    (r1 :> q1) @@ (r2 :> q1) @@ (r3 :> q1)

MCClientOf == 
    (r1 :> c1) @@ (r2 :> c1) @@ (r3 :> c1)

MCProtocolOf == 
    (r1 :> "REST") @@ (r2 :> "REST") @@ (r3 :> "REST")

MCSecurityContextOf == 
    (r1 :> s1) @@ (r2 :> s1) @@ (r3 :> s1)

=============================================================================
--------------------------------- MODULE MC_safety_symmetry ---------------------------------
EXTENDS DataLakehouseGateway, TLC

\* Model value constant declarations matching the .cfg CONSTANTS block
CONSTANTS
    r1, r2,
    t1, t2,
    q1,
    s1, s2,
    c1,
    w1, w2,
    b1, b2,
    p1, p2

(***************************************************************************)
(* REQUEST ATTRIBUTE MAPPINGS                                              *)
(* r1 exercises the asynchronous REST path with tenant t1 and sec-ctx s1.  *)
(* r2 exercises the synchronous FLIGHT path with tenant t2 and sec-ctx s2. *)
(***************************************************************************)

MCRequestedTenantOf == 
    (r1 :> t1) @@ (r2 :> t2)

MCAuthenticatedTenantOf == 
    (r1 :> t1) @@ (r2 :> t2)

MCQueryOf == 
    (r1 :> q1) @@ (r2 :> q1)

MCClientOf == 
    (r1 :> c1) @@ (r2 :> c1)

MCProtocolOf == 
    (r1 :> "REST") @@ (r2 :> "FLIGHT")

MCSecurityContextOf == 
    (r1 :> s1) @@ (r2 :> s2)

(***************************************************************************)
(* SYMMETRY GROUPS                                                         *)
(* Collapses isomorphic worker executions, proxy shard routings, and       *)
(* object storage blob allocations into single equivalence classes.        *)
(***************************************************************************)
MCSymmetry == 
    Permutations({w1, w2}) 
        \cup Permutations({p1, p2}) 
        \cup Permutations({b1, b2})

=============================================================================
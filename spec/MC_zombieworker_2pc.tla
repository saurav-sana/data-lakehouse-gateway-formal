--------------------------------- MODULE MC_zombieworker_2pc ---------------------------------
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
(* A stripped-down, single-request topology to isolate the zombie worker   *)
(* race condition. We route r1 through the REST path so it can be claimed  *)
(* by w1, forcibly timed out, and retried by w2 to test epoch fencing.     *)
(***************************************************************************)

MCRequestedTenantOf == 
    (r1 :> t1)

MCAuthenticatedTenantOf == 
    (r1 :> t1)

MCQueryOf == 
    (r1 :> q1)

MCClientOf == 
    (r1 :> c1)

MCProtocolOf == 
    (r1 :> "REST")

MCSecurityContextOf == 
    (r1 :> s1)

=============================================================================
--------------------------------- MODULE MC_security_mutation ---------------------------------
EXTENDS DataLakehouseGateway, TLC

\* 1. Constant Declarations matching the MC.cfg
CONSTANTS
    r1, r2,
    t1, t2,
    q1,
    s1,
    c1,
    w1,
    b1,
    p1

(***************************************************************************)
(* REQUEST ATTRIBUTE MAPPINGS (THE CYBERATTACK SIMULATION)                 *)
(* r1 acts as a malicious actor: its JWT is for t1, but it requests t2.    *)
(* r2 acts as normal traffic.                                              *)
(***************************************************************************)

\* The untrusted payload requested by the client
MCRequestedTenantOf == 
    (r1 :> t2) @@ (r2 :> t2)

\* The cryptographically verified identity (e.g. from the JWT Signature)
MCAuthenticatedTenantOf == 
    (r1 :> t1) @@ (r2 :> t2)

MCQueryOf == 
    (r1 :> q1) @@ (r2 :> q1)

MCClientOf == 
    (r1 :> c1) @@ (r2 :> c1)

MCProtocolOf == 
    (r1 :> "REST") @@ (r2 :> "REST")

MCSecurityContextOf == 
    (r1 :> s1) @@ (r2 :> s1)

=============================================================================
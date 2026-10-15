--------------------------------- MODULE MC_snapshot_concurrent ---------------------------------
EXTENDS DataLakehouseGateway, TLC

\* 1. Constant Declarations matching the MC.cfg
CONSTANTS
    r1,
    t1,
    q1,
    s1,
    c1,
    w1,
    b1,
    p1

(***************************************************************************)
(* REQUEST ATTRIBUTE MAPPINGS                                              *)
(* A stripped-down, single-request topology.                               *)
(* We route r1 through the REST path to force it through the worker        *)
(* queue, allowing LakehouseETL to advance the snapshot concurrently while *)
(* the worker is executing the job.                                        *)
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
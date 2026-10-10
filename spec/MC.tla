---------------------------- MODULE MC ----------------------------
EXTENDS DataLakehouseGateway, TLC

\* Model values declared here and bound to themselves in MC.cfg.
CONSTANTS r1, r2, r3, r4, t1, t2, q1, s1, s2, c1

\* r1: FLIGHT, tenant t1, context s1
\* r2: REST,   tenant t1, context s1  (same query as r1: cache sharing)
\* r3: REST,   tenant t1, context s2  (same query, different security context)
\* r4: REST,   requests t2 but authenticated as t1 (mismatch -> UNAUTHORIZED)

MCRequestedTenantOf ==
    (r1 :> t1) @@ (r2 :> t1) @@ (r3 :> t1) @@ (r4 :> t2)

MCAuthenticatedTenantOf ==
    (r1 :> t1) @@ (r2 :> t1) @@ (r3 :> t1) @@ (r4 :> t1)

MCQueryOf ==
    (r1 :> q1) @@ (r2 :> q1) @@ (r3 :> q1) @@ (r4 :> q1)

MCClientOf ==
    (r1 :> c1) @@ (r2 :> c1) @@ (r3 :> c1) @@ (r4 :> c1)

MCProtocolOf ==
    (r1 :> "FLIGHT") @@ (r2 :> "REST") @@ (r3 :> "REST") @@ (r4 :> "REST")

MCSecurityContextOf ==
    (r1 :> s1) @@ (r2 :> s1) @@ (r3 :> s2) @@ (r4 :> s1)

=============================================================================

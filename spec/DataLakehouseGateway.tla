---------------------- MODULE DataLakehouseGateway ----------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* DATA LAKEHOUSE GATEWAY - 6-STAGE LIFECYCLE ARCHITECTURE MODEL (v5)      *)
(***************************************************************************)

CONSTANTS 
    Tenants, Clients, Requests, Queries, Workers, Blobs, ProxyNodes,
    MaxSnapshot, MaxAttempts, MaxCrashes, MaxTimeouts, ScaleOutThreshold,
    RequestedTenantOf,        
    AuthenticatedTenantOf,    
    QueryOf, ClientOf,
    ProtocolOf,               
    SecurityContextOf,
    FlightPopulatesCache,     
    MutantSkipTenantCheck     

ASSUME 
    /\ DOMAIN RequestedTenantOf = Requests
    /\ DOMAIN AuthenticatedTenantOf = Requests
    /\ DOMAIN QueryOf = Requests
    /\ DOMAIN ClientOf = Requests
    /\ DOMAIN ProtocolOf = Requests
    /\ DOMAIN SecurityContextOf = Requests
    /\ ProxyNodes /= {}
    /\ ScaleOutThreshold \in Nat
    /\ MaxSnapshot >= 1 /\ MaxAttempts >= 1
    /\ MaxCrashes \in Nat /\ MaxTimeouts \in Nat
    /\ FlightPopulatesCache \in BOOLEAN
    /\ MutantSkipTenantCheck \in BOOLEAN
    /\ Requests \cap Workers = {}

NONE == "NONE"

SecCtxs == {SecurityContextOf[r] : r \in Requests}
NoEntry == [valid |-> FALSE, blob_id |-> NONE]
FreeBlob == [
    allocated |-> FALSE, 
    staged |-> FALSE, 
    req |-> NONE, 
    epoch |-> 0, 
    tenant |-> NONE, 
    query |-> NONE, 
    version |-> 0, 
    security_context |-> NONE
]

(*--algorithm DataLakehouseGateway

variables 
    hash_ring \in [Tenants \X Queries -> ProxyNodes],
    catalog_snapshot = [t \in Tenants |-> 1],
    cache = [p \in ProxyNodes |-> 
                [t \in Tenants |-> 
                    [q \in Queries |-> 
                        [v \in 1..MaxSnapshot |->
                            [s \in SecCtxs |-> NoEntry]]]]],
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
    blob_storage = [b \in Blobs |-> FreeBlob],
    available_blobs = Blobs,
    worker_status = [w \in Workers |-> "OFFLINE"],
    client_received = [r \in Requests |-> 
                        [delivered        |-> FALSE,
                         released         |-> FALSE,
                         blob_id          |-> NONE,
                         tenant           |-> NONE,
                         query            |-> NONE,
                         version          |-> 0,
                         security_context |-> NONE]],
    commit_count = [r \in Requests |-> 0],
    lease_expired = [r \in Requests |-> FALSE], 
    crashes  = 0, timeouts = 0;

define
    Pending   == {"QUEUED", "CLAIMED", "RUNNING", "STAGED"}
    Active    == {"CLAIMED", "RUNNING", "STAGED"}
    Terminal  == {"ACCEPTED", "FAILED", "UNAUTHORIZED","CACHED"}
    AllStates == {"IDLE"} \cup Pending \cup Terminal

    EffTenant(r) == 
        IF MutantSkipTenantCheck 
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
        \E p \in ProxyNodes, t \in Tenants, q \in Queries, 
           v \in 1..MaxSnapshot, s \in SecCtxs :
            cache[p][t][q][v][s].valid /\ cache[p][t][q][v][s].blob_id = b

    BlobJobHeld(b) == 
        \E r \in Requests : jobs[r].blob_ptr = b /\ ~client_received[r].released
            
    BlobClientHeld(b) == 
        \E r \in Requests : client_received[r].delivered 
            /\ ~client_received[r].released 
            /\ client_received[r].blob_id = b

    StagedOrphan(b) == jobs[blob_storage[b].req].lease_epoch /= blob_storage[b].epoch

    GCable == {b \in Blobs :
                /\ blob_storage[b].allocated
                /\ IF blob_storage[b].staged
                   THEN StagedOrphan(b)
                   ELSE ~BlobCached(b) /\ ~BlobJobHeld(b) /\ ~BlobClientHeld(b)}

    ExpirableJobs == {r \in Requests : 
                        /\ jobs[r].state \in Active
                        /\ (worker_status[jobs[r].owner] /= "ACTIVE" \/ lease_expired[r])}

    CachedKeys == {k \in ProxyNodes \X Tenants \X Queries \X (1..MaxSnapshot) \X SecCtxs : 
                    cache[k[1]][k[2]][k[3]][k[4]][k[5]].valid}

    (***********************************************************************)
    (* STATE MUTATION HELPERS (Fixes Translator Alignment & PDF Overflow)  *)
    (***********************************************************************)
    Job_Unauthorized(j) == 
        [j EXCEPT !.state = "UNAUTHORIZED"]
    Job_Cached(j) == 
        [j EXCEPT !.state = "CACHED"]
        
    Job_Init(j, t, sc, v) == 
        [j EXCEPT !.tenant = t, !.security_context = sc, !.version = v]
                  
    Job_Flight_Accepted(j, b) == 
        [j EXCEPT !.state = "ACCEPTED", !.lease_epoch = 1, !.attempts = 1, 
                  !.blob_ptr = b, !.rls_applied = TRUE, !.executed_predicate_tenant = j.tenant]
                  
    Job_Enqueue(j) == 
        [j EXCEPT !.state = "QUEUED", !.attempts = j.attempts + 1]
                  
    Job_Claim(j, w) == 
        [j EXCEPT !.owner = w, !.state = "CLAIMED", !.lease_epoch = j.lease_epoch + 1]
                  
    Job_Run(j) == 
        [j EXCEPT !.state = "RUNNING", !.rls_applied = TRUE, 
                  !.executed_predicate_tenant = j.tenant]
                  
    Job_Stage(j, b) == 
        [j EXCEPT !.blob_ptr = b, !.state = "STAGED"]
                  
    Job_Accept(j) == 
        [j EXCEPT !.state = "ACCEPTED", !.owner = NONE]
                  
    Job_Retry(j) == 
        [j EXCEPT !.owner = NONE, !.state = "QUEUED", !.attempts = j.attempts + 1, 
                  !.lease_epoch = j.lease_epoch + 1, !.blob_ptr = NONE, 
                  !.rls_applied = FALSE, !.executed_predicate_tenant = NONE]
                  
    Job_Fail(j) == 
        [j EXCEPT !.owner = NONE, !.state = "FAILED", !.lease_epoch = j.lease_epoch + 1, 
                  !.blob_ptr = NONE, !.rls_applied = FALSE, !.executed_predicate_tenant = NONE]

    Client_Deliver(cr, b, t, q, v, sc) == 
        [cr EXCEPT !.delivered = TRUE, !.blob_id = b, !.tenant = t, 
                   !.query = q, !.version = v, !.security_context = sc]
                   
    Client_Release(cr) == 
        [cr EXCEPT !.released = TRUE]

    Blob_Flight(t, q, v, sc) == 
        [allocated |-> TRUE, staged |-> FALSE, req |-> NONE, epoch |-> 0, 
         tenant |-> t, query |-> q, version |-> v, security_context |-> sc]
         
    Blob_Stage(req, ep, t, q, v, sc) == 
        [allocated |-> TRUE, staged |-> TRUE, req |-> req, epoch |-> ep, 
         tenant |-> t, query |-> q, version |-> v, security_context |-> sc]
         
    Blob_Commit(b_val) == 
        [b_val EXCEPT !.staged = FALSE]
        
    ValidCache(b) == 
        [valid |-> TRUE, blob_id |-> b]

    InvalidateCache(old_cache, t, new_v) ==
        [p \in ProxyNodes |-> 
            [old_cache[p] EXCEPT ![t] = 
                [q \in Queries |-> 
                    [v \in 1..MaxSnapshot |-> 
                        [s \in SecCtxs |->
                            IF v < new_v 
                            THEN NoEntry 
                            ELSE old_cache[p][t][q][v][s]]]]]]

    (***********************************************************************)
    (* INVARIANTS                                                          *)
    (***********************************************************************)
    TypeOK == 
        /\ catalog_snapshot \in [Tenants -> 1..MaxSnapshot]
        /\ worker_status \in [Workers -> {"OFFLINE", "ACTIVE", "CRASHED"}]
        /\ hash_ring \in [Tenants \X Queries -> ProxyNodes]
        /\ \A p \in ProxyNodes, t \in Tenants, q \in Queries, 
              v \in 1..MaxSnapshot, s \in SecCtxs :
              cache[p][t][q][v][s].valid \in BOOLEAN
        /\ \A r \in Requests :
              /\ jobs[r].state \in AllStates
              /\ jobs[r].attempts \in 0..MaxAttempts
              /\ jobs[r].lease_epoch \in Nat
              /\ jobs[r].blob_ptr \in Blobs \cup {NONE}
              /\ commit_count[r] \in 0..1
              /\ client_received[r].delivered => client_received[r].blob_id /= NONE

    TenantBinding == 
        \A r \in Requests : 
            jobs[r].state \notin {"IDLE", "UNAUTHORIZED","CACHED"} =>
                /\ jobs[r].tenant = AuthenticatedTenantOf[r]
                /\ jobs[r].security_context = SecurityContextOf[r]

    RLSEnforcement == 
        \A r \in Requests : 
            jobs[r].state \in {"RUNNING", "STAGED", "ACCEPTED"} =>
                /\ jobs[r].rls_applied
                /\ jobs[r].executed_predicate_tenant = AuthenticatedTenantOf[r]

    UnauthorizedIsInert == 
        \A r \in Requests : 
            jobs[r].state = "UNAUTHORIZED" =>
                /\ jobs[r].blob_ptr = NONE
                /\ jobs[r].owner = NONE
                /\ jobs[r].attempts = 0
                /\ commit_count[r] = 0
                /\ ~client_received[r].delivered
                /\ QCount(r) = 0

    MismatchRejected == 
        \A r \in Requests : 
            RequestedTenantOf[r] /= AuthenticatedTenantOf[r] =>
                /\ jobs[r].state \in {"IDLE", "UNAUTHORIZED"}
                /\ ~client_received[r].delivered

    TenantIsolation == 
        \A r \in Requests :
            client_received[r].delivered =>
                /\ client_received[r].tenant = AuthenticatedTenantOf[r]
                /\ client_received[r].security_context = SecurityContextOf[r]
                /\ client_received[r].query = QueryOf[r]

    DeliveredResultIntegrity == 
        \A r \in Requests :
            (client_received[r].delivered /\ ~client_received[r].released) =>
                /\ blob_storage[client_received[r].blob_id].allocated
                /\ ~blob_storage[client_received[r].blob_id].staged
                /\ BlobMatches(client_received[r].blob_id, 
                               AuthenticatedTenantOf[r], QueryOf[r], 
                               client_received[r].version, SecurityContextOf[r])

    ClaimCheckIntegrity == 
        \A r \in Requests :
            (jobs[r].state = "ACCEPTED" /\ ~client_received[r].released) =>
                /\ blob_storage[jobs[r].blob_ptr].allocated
                /\ ~blob_storage[jobs[r].blob_ptr].staged
                /\ BlobMatches(jobs[r].blob_ptr, jobs[r].tenant, jobs[r].query, 
                               jobs[r].version, jobs[r].security_context)

    BlobPtrIffResultState == 
        \A r \in Requests :
            (jobs[r].blob_ptr /= NONE) <=> 
                (jobs[r].state \in {"STAGED", "ACCEPTED"})

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

    CacheIntegrity == 
        \A p \in ProxyNodes, t \in Tenants, q \in Queries, 
           v \in 1..MaxSnapshot, s \in SecCtxs :
            cache[p][t][q][v][s].valid =>
                /\ blob_storage[cache[p][t][q][v][s].blob_id].allocated
                /\ ~blob_storage[cache[p][t][q][v][s].blob_id].staged
                /\ BlobMatches(cache[p][t][q][v][s].blob_id, t, q, v, s)

    CacheFreshness == 
        \A p \in ProxyNodes, t \in Tenants, q \in Queries, 
           v \in 1..MaxSnapshot, s \in SecCtxs :
            cache[p][t][q][v][s].valid => v = catalog_snapshot[t]

    ExactlyOnceCommit == 
        \A r \in Requests :
            /\ commit_count[r] <= 1
            /\ (jobs[r].state = "ACCEPTED") <=> (commit_count[r] = 1)

    FailedImpliesExhausted == 
        \A r \in Requests :
            jobs[r].state = "FAILED" => jobs[r].attempts = MaxAttempts

    LeaseOwnership == 
        \A r \in Requests :
            /\ jobs[r].state \in Active => jobs[r].owner \in Workers
            /\ jobs[r].state \notin Active => jobs[r].owner = NONE

    QueueConsistency == 
        \A r \in Requests :
            /\ jobs[r].state = "QUEUED" => QCount(r) = 1
            /\ jobs[r].state /= "QUEUED" => QCount(r) = 0

    FlightIsLocal == 
        \A r \in Requests :
            ProtocolOf[r] = "FLIGHT" =>
                /\ jobs[r].state \in {"IDLE", "ACCEPTED", "UNAUTHORIZED"}
                /\ jobs[r].owner = NONE
                /\ QCount(r) = 0

    SnapshotBound == 
        \A r \in Requests :
            /\ jobs[r].state \notin {"IDLE", "UNAUTHORIZED","CACHED"} =>
                   jobs[r].version \in 1..catalog_snapshot[jobs[r].tenant]
            /\ client_received[r].delivered =>
                   client_received[r].version 
                       \in 1..catalog_snapshot[AuthenticatedTenantOf[r]]
end define;


(***************************************************************************)
(* CLIENT / GATEWAY FRONT END                                              *)
(***************************************************************************)
fair process ClientProcess \in Requests
variables req_version = 0, proxy = NONE;
begin
Start:
    if ~MutantSkipTenantCheck /\ AuthenticatedTenantOf[self] /= RequestedTenantOf[self] then
        jobs[self] := Job_Unauthorized(jobs[self]);
        goto Finish;
    end if;

BindSnapshot:
    req_version := catalog_snapshot[EffTenant(self)];
    proxy := hash_ring[EffTenant(self), QueryOf[self]];

CheckCache:
    if cache[proxy][EffTenant(self)][QueryOf[self]][req_version][SecurityContextOf[self]].valid then
        client_received[self] := Client_Deliver(client_received[self], 
            cache[proxy][EffTenant(self)][QueryOf[self]][req_version][SecurityContextOf[self]].blob_id,
            EffTenant(self), QueryOf[self], req_version, SecurityContextOf[self]);
        \* FIX: Mark the job as ACCEPTED so the liveness state machine terminates correctly.
        jobs[self] := Job_Cached(jobs[self]); \* Marks job as terminating via Cache Short-Circuit
        goto Finish;
    end if;

InitializeJob:
    jobs[self] := Job_Init(jobs[self], EffTenant(self), SecurityContextOf[self], req_version);

Route:
    if ProtocolOf[self] = "FLIGHT" then goto ExecuteFlight; else goto EnqueueREST; end if;

ExecuteFlight:
    await available_blobs /= {};
    with b \in available_blobs do
        available_blobs := available_blobs \ {b};
        blob_storage[b] := Blob_Flight(jobs[self].tenant, jobs[self].query, jobs[self].version, jobs[self].security_context);
        jobs[self] := Job_Flight_Accepted(jobs[self], b);
        commit_count[self] := commit_count[self] + 1;
        client_received[self] := Client_Deliver(client_received[self], b, jobs[self].tenant, jobs[self].query, jobs[self].version, jobs[self].security_context);
            
        if FlightPopulatesCache /\ jobs[self].version = catalog_snapshot[jobs[self].tenant] then
            cache[proxy][jobs[self].tenant][jobs[self].query]
                 [jobs[self].version][jobs[self].security_context] := ValidCache(b);
        end if;
    end with;
    goto Finish;

EnqueueREST:
    jobs[self] := Job_Enqueue(jobs[self]);
    task_queue := Append(task_queue, self);

AwaitREST:
    await jobs[self].state \in Terminal;
    if jobs[self].state = "ACCEPTED" then
        client_received[self] := Client_Deliver(client_received[self], jobs[self].blob_ptr, jobs[self].tenant, jobs[self].query, jobs[self].version, jobs[self].security_context);
    end if;

Finish:
    if client_received[self].delivered then
        ReleaseBlob:
            client_received[self] := Client_Release(client_received[self]);
    end if;
end process;



(***************************************************************************)
(* REST COMPUTE WORKER                                                     *)
(***************************************************************************)
fair process ComputeWorker \in Workers
variables curr_req = NONE, curr_epoch = 0, curr_blob = NONE, curr_proxy = NONE;
begin
ClaimTask:
    while TRUE do
        await Len(task_queue) > 0 /\ worker_status[self] = "ACTIVE";
        with r = Head(task_queue) do
            task_queue := Tail(task_queue);
            curr_req := r;
            curr_blob := NONE;
            if jobs[r].state = "QUEUED" then
                curr_epoch := jobs[r].lease_epoch + 1;
                jobs[r] := Job_Claim(jobs[r], self);
            else 
                curr_epoch := 0; 
            end if;
        end with;

StartExecution:
        if curr_epoch > 0 /\ worker_status[self] = "ACTIVE" /\ HoldsLease(curr_req, curr_epoch, self, "CLAIMED") then
            jobs[curr_req] := Job_Run(jobs[curr_req]);
        else goto ClaimTask; end if;

AllocateBlob:
        await worker_status[self] /= "ACTIVE" \/ ~HoldsLease(curr_req, curr_epoch, self, "RUNNING") \/ available_blobs /= {};
        if worker_status[self] = "ACTIVE" /\ HoldsLease(curr_req, curr_epoch, self, "RUNNING") /\ available_blobs /= {} then
            with b \in available_blobs do
                available_blobs := available_blobs \ {b};
                curr_blob := b;
                blob_storage[b] := Blob_Stage(curr_req, curr_epoch, jobs[curr_req].tenant, jobs[curr_req].query, jobs[curr_req].version, jobs[curr_req].security_context);
            end with;
        else goto ClaimTask; end if;

PublishPointer:
        if worker_status[self] = "ACTIVE" /\ HoldsLease(curr_req, curr_epoch, self, "RUNNING") then
            jobs[curr_req] := Job_Stage(jobs[curr_req], curr_blob);
        else goto ClaimTask; end if;

CommitJob:
        if worker_status[self] = "ACTIVE" /\ HoldsLease(curr_req, curr_epoch, self, "STAGED") then
            jobs[curr_req] := Job_Accept(jobs[curr_req]);
            blob_storage[curr_blob] := Blob_Commit(blob_storage[curr_blob]);
            commit_count[curr_req] := commit_count[curr_req] + 1;
        else goto ClaimTask; end if;

PopulateCache:
        if worker_status[self] = "ACTIVE" 
           /\ jobs[curr_req].state = "ACCEPTED" 
           /\ jobs[curr_req].blob_ptr = curr_blob 
           /\ blob_storage[curr_blob].allocated
           /\ ~blob_storage[curr_blob].staged
           /\ BlobMatches(curr_blob, jobs[curr_req].tenant, jobs[curr_req].query, 
                          jobs[curr_req].version, jobs[curr_req].security_context)
           /\ jobs[curr_req].version = catalog_snapshot[jobs[curr_req].tenant] then
           
            curr_proxy := hash_ring[jobs[curr_req].tenant, jobs[curr_req].query];
            
            cache[curr_proxy][jobs[curr_req].tenant][jobs[curr_req].query]
                 [jobs[curr_req].version][jobs[curr_req].security_context] := ValidCache(curr_blob);
        end if;
    end while;
end process;

(***************************************************************************)
(* KEDA AUTOSCALER (Dynamic scale out / scale in)                          *)
(***************************************************************************)
fair process KedaAutoscaler = "KedaAutoscaler"
begin
ScaleLoop:
    while TRUE do
        either
            await Len(task_queue) >= ScaleOutThreshold 
                  /\ \E w \in Workers : worker_status[w] = "OFFLINE";
            with w \in {x \in Workers : worker_status[x] = "OFFLINE"} do
                worker_status[w] := "ACTIVE";
            end with;
        or
            await Len(task_queue) = 0 
                  /\ \E w \in Workers : worker_status[w] = "ACTIVE" 
                        /\ \A r \in Requests : ~(jobs[r].owner = w /\ jobs[r].state \in Active);
            with w \in {x \in Workers : worker_status[x] = "ACTIVE" 
                          /\ \A r \in Requests : ~(jobs[r].owner = x /\ jobs[r].state \in Active)} do
                worker_status[w] := "OFFLINE";
            end with;
        end either;
    end while;
end process;

(***************************************************************************)
(* CHAOS: LIVE WORKER TIMEOUTS (bounded by MaxTimeouts)                    *)
(***************************************************************************)
process TimeoutInjector = "TimeoutInjector"
begin
InjectLoop:
    while timeouts < MaxTimeouts do
        with r \in {x \in Requests : jobs[x].state \in Active /\ worker_status[jobs[x].owner] = "ACTIVE" /\ ~lease_expired[x]} do
            lease_expired[r] := TRUE;
            timeouts := timeouts + 1;
        end with;
    end while;
end process;

(***************************************************************************)
(* LEASE MANAGER                                                           *)
(***************************************************************************)
fair process LeaseManager = "LeaseManager"
begin
LeaseLoop:
    while TRUE do
        either
            \* Process genuine expirations for currently Active jobs
            with r \in ExpirableJobs do
                if jobs[r].attempts < MaxAttempts then
                    jobs[r] := Job_Retry(jobs[r]);
                    task_queue := Append(task_queue, r);
                else
                    jobs[r] := Job_Fail(jobs[r]);
                end if;
                lease_expired[r] := FALSE;
            end with;
        or
            \* Clear stale timeout flags for jobs that finished before the manager woke up
            with r \in {x \in Requests : jobs[x].state \notin Active /\ lease_expired[x]} do
                lease_expired[r] := FALSE;
            end with;
        end either;
    end while;
end process;

(***************************************************************************)
(* CHAOS: WORKER CRASHES & RECOVERY (Kubernetes Lifecycle)                 *)
(***************************************************************************)
process Crasher = "Crasher"
begin
CrashLoop:
    while crashes < MaxCrashes do
        await \E w \in Workers : worker_status[w] = "ACTIVE";
        with w \in {x \in Workers : worker_status[x] = "ACTIVE"} do
            worker_status[w] := "CRASHED";
            crashes := crashes + 1;
        end with;
    end while;
end process;

fair process Recoverer = "Recoverer"
begin
RecoverLoop:
    while TRUE do
        await \E w \in Workers : worker_status[w] = "CRASHED";
        with w \in {x \in Workers : worker_status[x] = "CRASHED"} do
            worker_status[w] := "OFFLINE";
        end with;
    end while;
end process;

(***************************************************************************)
(* GC, CACHE EVICTION, AND LAKEHOUSE ETL                                   *)
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

fair process CacheEvictor = "CacheEvictor"
begin 
EvictLoop: 
    while TRUE do 
        with e \in CachedKeys do 
            cache[e[1]][e[2]][e[3]][e[4]][e[5]] := NoEntry; 
        end with; 
    end while; 
end process;

fair process LakehouseETL = "LakehouseETL"
begin
ETLCommit:
    while TRUE do
        with t \in {x \in Tenants : catalog_snapshot[x] < MaxSnapshot} do
            cache := InvalidateCache(cache, t, catalog_snapshot[t] + 1);
            catalog_snapshot[t] := catalog_snapshot[t] + 1;
        end with;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES pc, hash_ring, catalog_snapshot, cache, task_queue, jobs, 
          blob_storage, available_blobs, worker_status, client_received, 
          commit_count, lease_expired, crashes, timeouts

(* define statement *)
Pending   == {"QUEUED", "CLAIMED", "RUNNING", "STAGED"}
Active    == {"CLAIMED", "RUNNING", "STAGED"}
Terminal  == {"ACCEPTED", "FAILED", "UNAUTHORIZED","CACHED"}
AllStates == {"IDLE"} \cup Pending \cup Terminal

EffTenant(r) ==
    IF MutantSkipTenantCheck
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
    \E p \in ProxyNodes, t \in Tenants, q \in Queries,
       v \in 1..MaxSnapshot, s \in SecCtxs :
        cache[p][t][q][v][s].valid /\ cache[p][t][q][v][s].blob_id = b

BlobJobHeld(b) ==
    \E r \in Requests : jobs[r].blob_ptr = b /\ ~client_received[r].released

BlobClientHeld(b) ==
    \E r \in Requests : client_received[r].delivered
        /\ ~client_received[r].released
        /\ client_received[r].blob_id = b

StagedOrphan(b) == jobs[blob_storage[b].req].lease_epoch /= blob_storage[b].epoch

GCable == {b \in Blobs :
            /\ blob_storage[b].allocated
            /\ IF blob_storage[b].staged
               THEN StagedOrphan(b)
               ELSE ~BlobCached(b) /\ ~BlobJobHeld(b) /\ ~BlobClientHeld(b)}

ExpirableJobs == {r \in Requests :
                    /\ jobs[r].state \in Active
                    /\ (worker_status[jobs[r].owner] /= "ACTIVE" \/ lease_expired[r])}

CachedKeys == {k \in ProxyNodes \X Tenants \X Queries \X (1..MaxSnapshot) \X SecCtxs :
                cache[k[1]][k[2]][k[3]][k[4]][k[5]].valid}




Job_Unauthorized(j) ==
    [j EXCEPT !.state = "UNAUTHORIZED"]
Job_Cached(j) ==
    [j EXCEPT !.state = "CACHED"]

Job_Init(j, t, sc, v) ==
    [j EXCEPT !.tenant = t, !.security_context = sc, !.version = v]

Job_Flight_Accepted(j, b) ==
    [j EXCEPT !.state = "ACCEPTED", !.lease_epoch = 1, !.attempts = 1,
              !.blob_ptr = b, !.rls_applied = TRUE, !.executed_predicate_tenant = j.tenant]

Job_Enqueue(j) ==
    [j EXCEPT !.state = "QUEUED", !.attempts = j.attempts + 1]

Job_Claim(j, w) ==
    [j EXCEPT !.owner = w, !.state = "CLAIMED", !.lease_epoch = j.lease_epoch + 1]

Job_Run(j) ==
    [j EXCEPT !.state = "RUNNING", !.rls_applied = TRUE,
              !.executed_predicate_tenant = j.tenant]

Job_Stage(j, b) ==
    [j EXCEPT !.blob_ptr = b, !.state = "STAGED"]

Job_Accept(j) ==
    [j EXCEPT !.state = "ACCEPTED", !.owner = NONE]

Job_Retry(j) ==
    [j EXCEPT !.owner = NONE, !.state = "QUEUED", !.attempts = j.attempts + 1,
              !.lease_epoch = j.lease_epoch + 1, !.blob_ptr = NONE,
              !.rls_applied = FALSE, !.executed_predicate_tenant = NONE]

Job_Fail(j) ==
    [j EXCEPT !.owner = NONE, !.state = "FAILED", !.lease_epoch = j.lease_epoch + 1,
              !.blob_ptr = NONE, !.rls_applied = FALSE, !.executed_predicate_tenant = NONE]

Client_Deliver(cr, b, t, q, v, sc) ==
    [cr EXCEPT !.delivered = TRUE, !.blob_id = b, !.tenant = t,
               !.query = q, !.version = v, !.security_context = sc]

Client_Release(cr) ==
    [cr EXCEPT !.released = TRUE]

Blob_Flight(t, q, v, sc) ==
    [allocated |-> TRUE, staged |-> FALSE, req |-> NONE, epoch |-> 0,
     tenant |-> t, query |-> q, version |-> v, security_context |-> sc]

Blob_Stage(req, ep, t, q, v, sc) ==
    [allocated |-> TRUE, staged |-> TRUE, req |-> req, epoch |-> ep,
     tenant |-> t, query |-> q, version |-> v, security_context |-> sc]

Blob_Commit(b_val) ==
    [b_val EXCEPT !.staged = FALSE]

ValidCache(b) ==
    [valid |-> TRUE, blob_id |-> b]

InvalidateCache(old_cache, t, new_v) ==
    [p \in ProxyNodes |->
        [old_cache[p] EXCEPT ![t] =
            [q \in Queries |->
                [v \in 1..MaxSnapshot |->
                    [s \in SecCtxs |->
                        IF v < new_v
                        THEN NoEntry
                        ELSE old_cache[p][t][q][v][s]]]]]]




TypeOK ==
    /\ catalog_snapshot \in [Tenants -> 1..MaxSnapshot]
    /\ worker_status \in [Workers -> {"OFFLINE", "ACTIVE", "CRASHED"}]
    /\ hash_ring \in [Tenants \X Queries -> ProxyNodes]
    /\ \A p \in ProxyNodes, t \in Tenants, q \in Queries,
          v \in 1..MaxSnapshot, s \in SecCtxs :
          cache[p][t][q][v][s].valid \in BOOLEAN
    /\ \A r \in Requests :
          /\ jobs[r].state \in AllStates
          /\ jobs[r].attempts \in 0..MaxAttempts
          /\ jobs[r].lease_epoch \in Nat
          /\ jobs[r].blob_ptr \in Blobs \cup {NONE}
          /\ commit_count[r] \in 0..1
          /\ client_received[r].delivered => client_received[r].blob_id /= NONE

TenantBinding ==
    \A r \in Requests :
        jobs[r].state \notin {"IDLE", "UNAUTHORIZED","CACHED"} =>
            /\ jobs[r].tenant = AuthenticatedTenantOf[r]
            /\ jobs[r].security_context = SecurityContextOf[r]

RLSEnforcement ==
    \A r \in Requests :
        jobs[r].state \in {"RUNNING", "STAGED", "ACCEPTED"} =>
            /\ jobs[r].rls_applied
            /\ jobs[r].executed_predicate_tenant = AuthenticatedTenantOf[r]

UnauthorizedIsInert ==
    \A r \in Requests :
        jobs[r].state = "UNAUTHORIZED" =>
            /\ jobs[r].blob_ptr = NONE
            /\ jobs[r].owner = NONE
            /\ jobs[r].attempts = 0
            /\ commit_count[r] = 0
            /\ ~client_received[r].delivered
            /\ QCount(r) = 0

MismatchRejected ==
    \A r \in Requests :
        RequestedTenantOf[r] /= AuthenticatedTenantOf[r] =>
            /\ jobs[r].state \in {"IDLE", "UNAUTHORIZED"}
            /\ ~client_received[r].delivered

TenantIsolation ==
    \A r \in Requests :
        client_received[r].delivered =>
            /\ client_received[r].tenant = AuthenticatedTenantOf[r]
            /\ client_received[r].security_context = SecurityContextOf[r]
            /\ client_received[r].query = QueryOf[r]

DeliveredResultIntegrity ==
    \A r \in Requests :
        (client_received[r].delivered /\ ~client_received[r].released) =>
            /\ blob_storage[client_received[r].blob_id].allocated
            /\ ~blob_storage[client_received[r].blob_id].staged
            /\ BlobMatches(client_received[r].blob_id,
                           AuthenticatedTenantOf[r], QueryOf[r],
                           client_received[r].version, SecurityContextOf[r])

ClaimCheckIntegrity ==
    \A r \in Requests :
        (jobs[r].state = "ACCEPTED" /\ ~client_received[r].released) =>
            /\ blob_storage[jobs[r].blob_ptr].allocated
            /\ ~blob_storage[jobs[r].blob_ptr].staged
            /\ BlobMatches(jobs[r].blob_ptr, jobs[r].tenant, jobs[r].query,
                           jobs[r].version, jobs[r].security_context)

BlobPtrIffResultState ==
    \A r \in Requests :
        (jobs[r].blob_ptr /= NONE) <=>
            (jobs[r].state \in {"STAGED", "ACCEPTED"})

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

CacheIntegrity ==
    \A p \in ProxyNodes, t \in Tenants, q \in Queries,
       v \in 1..MaxSnapshot, s \in SecCtxs :
        cache[p][t][q][v][s].valid =>
            /\ blob_storage[cache[p][t][q][v][s].blob_id].allocated
            /\ ~blob_storage[cache[p][t][q][v][s].blob_id].staged
            /\ BlobMatches(cache[p][t][q][v][s].blob_id, t, q, v, s)

CacheFreshness ==
    \A p \in ProxyNodes, t \in Tenants, q \in Queries,
       v \in 1..MaxSnapshot, s \in SecCtxs :
        cache[p][t][q][v][s].valid => v = catalog_snapshot[t]

ExactlyOnceCommit ==
    \A r \in Requests :
        /\ commit_count[r] <= 1
        /\ (jobs[r].state = "ACCEPTED") <=> (commit_count[r] = 1)

FailedImpliesExhausted ==
    \A r \in Requests :
        jobs[r].state = "FAILED" => jobs[r].attempts = MaxAttempts

LeaseOwnership ==
    \A r \in Requests :
        /\ jobs[r].state \in Active => jobs[r].owner \in Workers
        /\ jobs[r].state \notin Active => jobs[r].owner = NONE

QueueConsistency ==
    \A r \in Requests :
        /\ jobs[r].state = "QUEUED" => QCount(r) = 1
        /\ jobs[r].state /= "QUEUED" => QCount(r) = 0

FlightIsLocal ==
    \A r \in Requests :
        ProtocolOf[r] = "FLIGHT" =>
            /\ jobs[r].state \in {"IDLE", "ACCEPTED", "UNAUTHORIZED"}
            /\ jobs[r].owner = NONE
            /\ QCount(r) = 0

SnapshotBound ==
    \A r \in Requests :
        /\ jobs[r].state \notin {"IDLE", "UNAUTHORIZED","CACHED"} =>
               jobs[r].version \in 1..catalog_snapshot[jobs[r].tenant]
        /\ client_received[r].delivered =>
               client_received[r].version
                   \in 1..catalog_snapshot[AuthenticatedTenantOf[r]]

VARIABLES req_version, proxy, curr_req, curr_epoch, curr_blob, curr_proxy

vars == << pc, hash_ring, catalog_snapshot, cache, task_queue, jobs, 
           blob_storage, available_blobs, worker_status, client_received, 
           commit_count, lease_expired, crashes, timeouts, req_version, proxy, 
           curr_req, curr_epoch, curr_blob, curr_proxy >>

ProcSet == (Requests) \cup (Workers) \cup {"KedaAutoscaler"} \cup {"TimeoutInjector"} \cup {"LeaseManager"} \cup {"Crasher"} \cup {"Recoverer"} \cup {"GarbageCollector"} \cup {"CacheEvictor"} \cup {"LakehouseETL"}

Init == (* Global variables *)
        /\ hash_ring \in [Tenants \X Queries -> ProxyNodes]
        /\ catalog_snapshot = [t \in Tenants |-> 1]
        /\ cache = [p \in ProxyNodes |->
                       [t \in Tenants |->
                           [q \in Queries |->
                               [v \in 1..MaxSnapshot |->
                                   [s \in SecCtxs |-> NoEntry]]]]]
        /\ task_queue = << >>
        /\ jobs = [r \in Requests |->
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
                    executed_predicate_tenant |-> NONE]]
        /\ blob_storage = [b \in Blobs |-> FreeBlob]
        /\ available_blobs = Blobs
        /\ worker_status = [w \in Workers |-> "OFFLINE"]
        /\ client_received = [r \in Requests |->
                               [delivered        |-> FALSE,
                                released         |-> FALSE,
                                blob_id          |-> NONE,
                                tenant           |-> NONE,
                                query            |-> NONE,
                                version          |-> 0,
                                security_context |-> NONE]]
        /\ commit_count = [r \in Requests |-> 0]
        /\ lease_expired = [r \in Requests |-> FALSE]
        /\ crashes = 0
        /\ timeouts = 0
        (* Process ClientProcess *)
        /\ req_version = [self \in Requests |-> 0]
        /\ proxy = [self \in Requests |-> NONE]
        (* Process ComputeWorker *)
        /\ curr_req = [self \in Workers |-> NONE]
        /\ curr_epoch = [self \in Workers |-> 0]
        /\ curr_blob = [self \in Workers |-> NONE]
        /\ curr_proxy = [self \in Workers |-> NONE]
        /\ pc = [self \in ProcSet |-> CASE self \in Requests -> "Start"
                                        [] self \in Workers -> "ClaimTask"
                                        [] self = "KedaAutoscaler" -> "ScaleLoop"
                                        [] self = "TimeoutInjector" -> "InjectLoop"
                                        [] self = "LeaseManager" -> "LeaseLoop"
                                        [] self = "Crasher" -> "CrashLoop"
                                        [] self = "Recoverer" -> "RecoverLoop"
                                        [] self = "GarbageCollector" -> "GCLoop"
                                        [] self = "CacheEvictor" -> "EvictLoop"
                                        [] self = "LakehouseETL" -> "ETLCommit"]

Start(self) == /\ pc[self] = "Start"
               /\ IF ~MutantSkipTenantCheck /\ AuthenticatedTenantOf[self] /= RequestedTenantOf[self]
                     THEN /\ jobs' = [jobs EXCEPT ![self] = Job_Unauthorized(jobs[self])]
                          /\ pc' = [pc EXCEPT ![self] = "Finish"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "BindSnapshot"]
                          /\ jobs' = jobs
               /\ UNCHANGED << hash_ring, catalog_snapshot, cache, task_queue, 
                               blob_storage, available_blobs, worker_status, 
                               client_received, commit_count, lease_expired, 
                               crashes, timeouts, req_version, proxy, curr_req, 
                               curr_epoch, curr_blob, curr_proxy >>

BindSnapshot(self) == /\ pc[self] = "BindSnapshot"
                      /\ req_version' = [req_version EXCEPT ![self] = catalog_snapshot[EffTenant(self)]]
                      /\ proxy' = [proxy EXCEPT ![self] = hash_ring[EffTenant(self), QueryOf[self]]]
                      /\ pc' = [pc EXCEPT ![self] = "CheckCache"]
                      /\ UNCHANGED << hash_ring, catalog_snapshot, cache, 
                                      task_queue, jobs, blob_storage, 
                                      available_blobs, worker_status, 
                                      client_received, commit_count, 
                                      lease_expired, crashes, timeouts, 
                                      curr_req, curr_epoch, curr_blob, 
                                      curr_proxy >>

CheckCache(self) == /\ pc[self] = "CheckCache"
                    /\ IF cache[proxy[self]][EffTenant(self)][QueryOf[self]][req_version[self]][SecurityContextOf[self]].valid
                          THEN /\ client_received' = [client_received EXCEPT ![self] =                      Client_Deliver(client_received[self],
                                                                                       cache[proxy[self]][EffTenant(self)][QueryOf[self]][req_version[self]][SecurityContextOf[self]].blob_id,
                                                                                       EffTenant(self), QueryOf[self], req_version[self], SecurityContextOf[self])]
                               /\ jobs' = [jobs EXCEPT ![self] = Job_Cached(jobs[self])]
                               /\ pc' = [pc EXCEPT ![self] = "Finish"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "InitializeJob"]
                               /\ UNCHANGED << jobs, client_received >>
                    /\ UNCHANGED << hash_ring, catalog_snapshot, cache, 
                                    task_queue, blob_storage, available_blobs, 
                                    worker_status, commit_count, lease_expired, 
                                    crashes, timeouts, req_version, proxy, 
                                    curr_req, curr_epoch, curr_blob, 
                                    curr_proxy >>

InitializeJob(self) == /\ pc[self] = "InitializeJob"
                       /\ jobs' = [jobs EXCEPT ![self] = Job_Init(jobs[self], EffTenant(self), SecurityContextOf[self], req_version[self])]
                       /\ pc' = [pc EXCEPT ![self] = "Route"]
                       /\ UNCHANGED << hash_ring, catalog_snapshot, cache, 
                                       task_queue, blob_storage, 
                                       available_blobs, worker_status, 
                                       client_received, commit_count, 
                                       lease_expired, crashes, timeouts, 
                                       req_version, proxy, curr_req, 
                                       curr_epoch, curr_blob, curr_proxy >>

Route(self) == /\ pc[self] = "Route"
               /\ IF ProtocolOf[self] = "FLIGHT"
                     THEN /\ pc' = [pc EXCEPT ![self] = "ExecuteFlight"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "EnqueueREST"]
               /\ UNCHANGED << hash_ring, catalog_snapshot, cache, task_queue, 
                               jobs, blob_storage, available_blobs, 
                               worker_status, client_received, commit_count, 
                               lease_expired, crashes, timeouts, req_version, 
                               proxy, curr_req, curr_epoch, curr_blob, 
                               curr_proxy >>

ExecuteFlight(self) == /\ pc[self] = "ExecuteFlight"
                       /\ available_blobs /= {}
                       /\ \E b \in available_blobs:
                            /\ available_blobs' = available_blobs \ {b}
                            /\ blob_storage' = [blob_storage EXCEPT ![b] = Blob_Flight(jobs[self].tenant, jobs[self].query, jobs[self].version, jobs[self].security_context)]
                            /\ jobs' = [jobs EXCEPT ![self] = Job_Flight_Accepted(jobs[self], b)]
                            /\ commit_count' = [commit_count EXCEPT ![self] = commit_count[self] + 1]
                            /\ client_received' = [client_received EXCEPT ![self] = Client_Deliver(client_received[self], b, jobs'[self].tenant, jobs'[self].query, jobs'[self].version, jobs'[self].security_context)]
                            /\ IF FlightPopulatesCache /\ jobs'[self].version = catalog_snapshot[jobs'[self].tenant]
                                  THEN /\ cache' = [cache EXCEPT ![proxy[self]][jobs'[self].tenant][jobs'[self].query]
                                                                  [jobs'[self].version][jobs'[self].security_context] = ValidCache(b)]
                                  ELSE /\ TRUE
                                       /\ cache' = cache
                       /\ pc' = [pc EXCEPT ![self] = "Finish"]
                       /\ UNCHANGED << hash_ring, catalog_snapshot, task_queue, 
                                       worker_status, lease_expired, crashes, 
                                       timeouts, req_version, proxy, curr_req, 
                                       curr_epoch, curr_blob, curr_proxy >>

EnqueueREST(self) == /\ pc[self] = "EnqueueREST"
                     /\ jobs' = [jobs EXCEPT ![self] = Job_Enqueue(jobs[self])]
                     /\ task_queue' = Append(task_queue, self)
                     /\ pc' = [pc EXCEPT ![self] = "AwaitREST"]
                     /\ UNCHANGED << hash_ring, catalog_snapshot, cache, 
                                     blob_storage, available_blobs, 
                                     worker_status, client_received, 
                                     commit_count, lease_expired, crashes, 
                                     timeouts, req_version, proxy, curr_req, 
                                     curr_epoch, curr_blob, curr_proxy >>

AwaitREST(self) == /\ pc[self] = "AwaitREST"
                   /\ jobs[self].state \in Terminal
                   /\ IF jobs[self].state = "ACCEPTED"
                         THEN /\ client_received' = [client_received EXCEPT ![self] = Client_Deliver(client_received[self], jobs[self].blob_ptr, jobs[self].tenant, jobs[self].query, jobs[self].version, jobs[self].security_context)]
                         ELSE /\ TRUE
                              /\ UNCHANGED client_received
                   /\ pc' = [pc EXCEPT ![self] = "Finish"]
                   /\ UNCHANGED << hash_ring, catalog_snapshot, cache, 
                                   task_queue, jobs, blob_storage, 
                                   available_blobs, worker_status, 
                                   commit_count, lease_expired, crashes, 
                                   timeouts, req_version, proxy, curr_req, 
                                   curr_epoch, curr_blob, curr_proxy >>

Finish(self) == /\ pc[self] = "Finish"
                /\ IF client_received[self].delivered
                      THEN /\ pc' = [pc EXCEPT ![self] = "ReleaseBlob"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << hash_ring, catalog_snapshot, cache, task_queue, 
                                jobs, blob_storage, available_blobs, 
                                worker_status, client_received, commit_count, 
                                lease_expired, crashes, timeouts, req_version, 
                                proxy, curr_req, curr_epoch, curr_blob, 
                                curr_proxy >>

ReleaseBlob(self) == /\ pc[self] = "ReleaseBlob"
                     /\ client_received' = [client_received EXCEPT ![self] = Client_Release(client_received[self])]
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << hash_ring, catalog_snapshot, cache, 
                                     task_queue, jobs, blob_storage, 
                                     available_blobs, worker_status, 
                                     commit_count, lease_expired, crashes, 
                                     timeouts, req_version, proxy, curr_req, 
                                     curr_epoch, curr_blob, curr_proxy >>

ClientProcess(self) == Start(self) \/ BindSnapshot(self)
                          \/ CheckCache(self) \/ InitializeJob(self)
                          \/ Route(self) \/ ExecuteFlight(self)
                          \/ EnqueueREST(self) \/ AwaitREST(self)
                          \/ Finish(self) \/ ReleaseBlob(self)

ClaimTask(self) == /\ pc[self] = "ClaimTask"
                   /\ Len(task_queue) > 0 /\ worker_status[self] = "ACTIVE"
                   /\ LET r == Head(task_queue) IN
                        /\ task_queue' = Tail(task_queue)
                        /\ curr_req' = [curr_req EXCEPT ![self] = r]
                        /\ curr_blob' = [curr_blob EXCEPT ![self] = NONE]
                        /\ IF jobs[r].state = "QUEUED"
                              THEN /\ curr_epoch' = [curr_epoch EXCEPT ![self] = jobs[r].lease_epoch + 1]
                                   /\ jobs' = [jobs EXCEPT ![r] = Job_Claim(jobs[r], self)]
                              ELSE /\ curr_epoch' = [curr_epoch EXCEPT ![self] = 0]
                                   /\ jobs' = jobs
                   /\ pc' = [pc EXCEPT ![self] = "StartExecution"]
                   /\ UNCHANGED << hash_ring, catalog_snapshot, cache, 
                                   blob_storage, available_blobs, 
                                   worker_status, client_received, 
                                   commit_count, lease_expired, crashes, 
                                   timeouts, req_version, proxy, curr_proxy >>

StartExecution(self) == /\ pc[self] = "StartExecution"
                        /\ IF curr_epoch[self] > 0 /\ worker_status[self] = "ACTIVE" /\ HoldsLease(curr_req[self], curr_epoch[self], self, "CLAIMED")
                              THEN /\ jobs' = [jobs EXCEPT ![curr_req[self]] = Job_Run(jobs[curr_req[self]])]
                                   /\ pc' = [pc EXCEPT ![self] = "AllocateBlob"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "ClaimTask"]
                                   /\ jobs' = jobs
                        /\ UNCHANGED << hash_ring, catalog_snapshot, cache, 
                                        task_queue, blob_storage, 
                                        available_blobs, worker_status, 
                                        client_received, commit_count, 
                                        lease_expired, crashes, timeouts, 
                                        req_version, proxy, curr_req, 
                                        curr_epoch, curr_blob, curr_proxy >>

AllocateBlob(self) == /\ pc[self] = "AllocateBlob"
                      /\ worker_status[self] /= "ACTIVE" \/ ~HoldsLease(curr_req[self], curr_epoch[self], self, "RUNNING") \/ available_blobs /= {}
                      /\ IF worker_status[self] = "ACTIVE" /\ HoldsLease(curr_req[self], curr_epoch[self], self, "RUNNING") /\ available_blobs /= {}
                            THEN /\ \E b \in available_blobs:
                                      /\ available_blobs' = available_blobs \ {b}
                                      /\ curr_blob' = [curr_blob EXCEPT ![self] = b]
                                      /\ blob_storage' = [blob_storage EXCEPT ![b] = Blob_Stage(curr_req[self], curr_epoch[self], jobs[curr_req[self]].tenant, jobs[curr_req[self]].query, jobs[curr_req[self]].version, jobs[curr_req[self]].security_context)]
                                 /\ pc' = [pc EXCEPT ![self] = "PublishPointer"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "ClaimTask"]
                                 /\ UNCHANGED << blob_storage, available_blobs, 
                                                 curr_blob >>
                      /\ UNCHANGED << hash_ring, catalog_snapshot, cache, 
                                      task_queue, jobs, worker_status, 
                                      client_received, commit_count, 
                                      lease_expired, crashes, timeouts, 
                                      req_version, proxy, curr_req, curr_epoch, 
                                      curr_proxy >>

PublishPointer(self) == /\ pc[self] = "PublishPointer"
                        /\ IF worker_status[self] = "ACTIVE" /\ HoldsLease(curr_req[self], curr_epoch[self], self, "RUNNING")
                              THEN /\ jobs' = [jobs EXCEPT ![curr_req[self]] = Job_Stage(jobs[curr_req[self]], curr_blob[self])]
                                   /\ pc' = [pc EXCEPT ![self] = "CommitJob"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "ClaimTask"]
                                   /\ jobs' = jobs
                        /\ UNCHANGED << hash_ring, catalog_snapshot, cache, 
                                        task_queue, blob_storage, 
                                        available_blobs, worker_status, 
                                        client_received, commit_count, 
                                        lease_expired, crashes, timeouts, 
                                        req_version, proxy, curr_req, 
                                        curr_epoch, curr_blob, curr_proxy >>

CommitJob(self) == /\ pc[self] = "CommitJob"
                   /\ IF worker_status[self] = "ACTIVE" /\ HoldsLease(curr_req[self], curr_epoch[self], self, "STAGED")
                         THEN /\ jobs' = [jobs EXCEPT ![curr_req[self]] = Job_Accept(jobs[curr_req[self]])]
                              /\ blob_storage' = [blob_storage EXCEPT ![curr_blob[self]] = Blob_Commit(blob_storage[curr_blob[self]])]
                              /\ commit_count' = [commit_count EXCEPT ![curr_req[self]] = commit_count[curr_req[self]] + 1]
                              /\ pc' = [pc EXCEPT ![self] = "PopulateCache"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "ClaimTask"]
                              /\ UNCHANGED << jobs, blob_storage, commit_count >>
                   /\ UNCHANGED << hash_ring, catalog_snapshot, cache, 
                                   task_queue, available_blobs, worker_status, 
                                   client_received, lease_expired, crashes, 
                                   timeouts, req_version, proxy, curr_req, 
                                   curr_epoch, curr_blob, curr_proxy >>

PopulateCache(self) == /\ pc[self] = "PopulateCache"
                       /\ IF worker_status[self] = "ACTIVE"
                             /\ jobs[curr_req[self]].state = "ACCEPTED"
                             /\ jobs[curr_req[self]].blob_ptr = curr_blob[self]
                             /\ blob_storage[curr_blob[self]].allocated
                             /\ ~blob_storage[curr_blob[self]].staged
                             /\ BlobMatches(curr_blob[self], jobs[curr_req[self]].tenant, jobs[curr_req[self]].query,
                                            jobs[curr_req[self]].version, jobs[curr_req[self]].security_context)
                             /\ jobs[curr_req[self]].version = catalog_snapshot[jobs[curr_req[self]].tenant]
                             THEN /\ curr_proxy' = [curr_proxy EXCEPT ![self] = hash_ring[jobs[curr_req[self]].tenant, jobs[curr_req[self]].query]]
                                  /\ cache' = [cache EXCEPT ![curr_proxy'[self]][jobs[curr_req[self]].tenant][jobs[curr_req[self]].query]
                                                             [jobs[curr_req[self]].version][jobs[curr_req[self]].security_context] = ValidCache(curr_blob[self])]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << cache, curr_proxy >>
                       /\ pc' = [pc EXCEPT ![self] = "ClaimTask"]
                       /\ UNCHANGED << hash_ring, catalog_snapshot, task_queue, 
                                       jobs, blob_storage, available_blobs, 
                                       worker_status, client_received, 
                                       commit_count, lease_expired, crashes, 
                                       timeouts, req_version, proxy, curr_req, 
                                       curr_epoch, curr_blob >>

ComputeWorker(self) == ClaimTask(self) \/ StartExecution(self)
                          \/ AllocateBlob(self) \/ PublishPointer(self)
                          \/ CommitJob(self) \/ PopulateCache(self)

ScaleLoop == /\ pc["KedaAutoscaler"] = "ScaleLoop"
             /\ \/ /\ Len(task_queue) >= ScaleOutThreshold
                      /\ \E w \in Workers : worker_status[w] = "OFFLINE"
                   /\ \E w \in {x \in Workers : worker_status[x] = "OFFLINE"}:
                        worker_status' = [worker_status EXCEPT ![w] = "ACTIVE"]
                \/ /\ Len(task_queue) = 0
                      /\ \E w \in Workers : worker_status[w] = "ACTIVE"
                            /\ \A r \in Requests : ~(jobs[r].owner = w /\ jobs[r].state \in Active)
                   /\ \E w \in {x \in Workers : worker_status[x] = "ACTIVE"
                                  /\ \A r \in Requests : ~(jobs[r].owner = x /\ jobs[r].state \in Active)}:
                        worker_status' = [worker_status EXCEPT ![w] = "OFFLINE"]
             /\ pc' = [pc EXCEPT !["KedaAutoscaler"] = "ScaleLoop"]
             /\ UNCHANGED << hash_ring, catalog_snapshot, cache, task_queue, 
                             jobs, blob_storage, available_blobs, 
                             client_received, commit_count, lease_expired, 
                             crashes, timeouts, req_version, proxy, curr_req, 
                             curr_epoch, curr_blob, curr_proxy >>

KedaAutoscaler == ScaleLoop

InjectLoop == /\ pc["TimeoutInjector"] = "InjectLoop"
              /\ IF timeouts < MaxTimeouts
                    THEN /\ \E r \in {x \in Requests : jobs[x].state \in Active /\ worker_status[jobs[x].owner] = "ACTIVE" /\ ~lease_expired[x]}:
                              /\ lease_expired' = [lease_expired EXCEPT ![r] = TRUE]
                              /\ timeouts' = timeouts + 1
                         /\ pc' = [pc EXCEPT !["TimeoutInjector"] = "InjectLoop"]
                    ELSE /\ pc' = [pc EXCEPT !["TimeoutInjector"] = "Done"]
                         /\ UNCHANGED << lease_expired, timeouts >>
              /\ UNCHANGED << hash_ring, catalog_snapshot, cache, task_queue, 
                              jobs, blob_storage, available_blobs, 
                              worker_status, client_received, commit_count, 
                              crashes, req_version, proxy, curr_req, 
                              curr_epoch, curr_blob, curr_proxy >>

TimeoutInjector == InjectLoop

LeaseLoop == /\ pc["LeaseManager"] = "LeaseLoop"
             /\ \/ /\ \E r \in ExpirableJobs:
                        /\ IF jobs[r].attempts < MaxAttempts
                              THEN /\ jobs' = [jobs EXCEPT ![r] = Job_Retry(jobs[r])]
                                   /\ task_queue' = Append(task_queue, r)
                              ELSE /\ jobs' = [jobs EXCEPT ![r] = Job_Fail(jobs[r])]
                                   /\ UNCHANGED task_queue
                        /\ lease_expired' = [lease_expired EXCEPT ![r] = FALSE]
                \/ /\ \E r \in {x \in Requests : jobs[x].state \notin Active /\ lease_expired[x]}:
                        lease_expired' = [lease_expired EXCEPT ![r] = FALSE]
                   /\ UNCHANGED <<task_queue, jobs>>
             /\ pc' = [pc EXCEPT !["LeaseManager"] = "LeaseLoop"]
             /\ UNCHANGED << hash_ring, catalog_snapshot, cache, blob_storage, 
                             available_blobs, worker_status, client_received, 
                             commit_count, crashes, timeouts, req_version, 
                             proxy, curr_req, curr_epoch, curr_blob, 
                             curr_proxy >>

LeaseManager == LeaseLoop

CrashLoop == /\ pc["Crasher"] = "CrashLoop"
             /\ IF crashes < MaxCrashes
                   THEN /\ \E w \in Workers : worker_status[w] = "ACTIVE"
                        /\ \E w \in {x \in Workers : worker_status[x] = "ACTIVE"}:
                             /\ worker_status' = [worker_status EXCEPT ![w] = "CRASHED"]
                             /\ crashes' = crashes + 1
                        /\ pc' = [pc EXCEPT !["Crasher"] = "CrashLoop"]
                   ELSE /\ pc' = [pc EXCEPT !["Crasher"] = "Done"]
                        /\ UNCHANGED << worker_status, crashes >>
             /\ UNCHANGED << hash_ring, catalog_snapshot, cache, task_queue, 
                             jobs, blob_storage, available_blobs, 
                             client_received, commit_count, lease_expired, 
                             timeouts, req_version, proxy, curr_req, 
                             curr_epoch, curr_blob, curr_proxy >>

Crasher == CrashLoop

RecoverLoop == /\ pc["Recoverer"] = "RecoverLoop"
               /\ \E w \in Workers : worker_status[w] = "CRASHED"
               /\ \E w \in {x \in Workers : worker_status[x] = "CRASHED"}:
                    worker_status' = [worker_status EXCEPT ![w] = "OFFLINE"]
               /\ pc' = [pc EXCEPT !["Recoverer"] = "RecoverLoop"]
               /\ UNCHANGED << hash_ring, catalog_snapshot, cache, task_queue, 
                               jobs, blob_storage, available_blobs, 
                               client_received, commit_count, lease_expired, 
                               crashes, timeouts, req_version, proxy, curr_req, 
                               curr_epoch, curr_blob, curr_proxy >>

Recoverer == RecoverLoop

GCLoop == /\ pc["GarbageCollector"] = "GCLoop"
          /\ \E b \in GCable:
               /\ blob_storage' = [blob_storage EXCEPT ![b] = FreeBlob]
               /\ available_blobs' = (available_blobs \union {b})
          /\ pc' = [pc EXCEPT !["GarbageCollector"] = "GCLoop"]
          /\ UNCHANGED << hash_ring, catalog_snapshot, cache, task_queue, jobs, 
                          worker_status, client_received, commit_count, 
                          lease_expired, crashes, timeouts, req_version, proxy, 
                          curr_req, curr_epoch, curr_blob, curr_proxy >>

GarbageCollector == GCLoop

EvictLoop == /\ pc["CacheEvictor"] = "EvictLoop"
             /\ \E e \in CachedKeys:
                  cache' = [cache EXCEPT ![e[1]][e[2]][e[3]][e[4]][e[5]] = NoEntry]
             /\ pc' = [pc EXCEPT !["CacheEvictor"] = "EvictLoop"]
             /\ UNCHANGED << hash_ring, catalog_snapshot, task_queue, jobs, 
                             blob_storage, available_blobs, worker_status, 
                             client_received, commit_count, lease_expired, 
                             crashes, timeouts, req_version, proxy, curr_req, 
                             curr_epoch, curr_blob, curr_proxy >>

CacheEvictor == EvictLoop

ETLCommit == /\ pc["LakehouseETL"] = "ETLCommit"
             /\ \E t \in {x \in Tenants : catalog_snapshot[x] < MaxSnapshot}:
                  /\ cache' = InvalidateCache(cache, t, catalog_snapshot[t] + 1)
                  /\ catalog_snapshot' = [catalog_snapshot EXCEPT ![t] = catalog_snapshot[t] + 1]
             /\ pc' = [pc EXCEPT !["LakehouseETL"] = "ETLCommit"]
             /\ UNCHANGED << hash_ring, task_queue, jobs, blob_storage, 
                             available_blobs, worker_status, client_received, 
                             commit_count, lease_expired, crashes, timeouts, 
                             req_version, proxy, curr_req, curr_epoch, 
                             curr_blob, curr_proxy >>

LakehouseETL == ETLCommit

Next == KedaAutoscaler \/ TimeoutInjector \/ LeaseManager \/ Crasher
           \/ Recoverer \/ GarbageCollector \/ CacheEvictor \/ LakehouseETL
           \/ (\E self \in Requests: ClientProcess(self))
           \/ (\E self \in Workers: ComputeWorker(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Requests : WF_vars(ClientProcess(self))
        /\ \A self \in Workers : WF_vars(ComputeWorker(self))
        /\ WF_vars(KedaAutoscaler)
        /\ WF_vars(LeaseManager)
        /\ WF_vars(Recoverer)
        /\ WF_vars(GarbageCollector)
        /\ WF_vars(CacheEvictor)
        /\ WF_vars(LakehouseETL)

\* END TRANSLATION
=============================================================================

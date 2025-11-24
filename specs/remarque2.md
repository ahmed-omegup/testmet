16bytes is the whole layout, we talked about this: 8 for the pointer 4 for the index key, and 4 for the id

Can you tell me how exactly we will be using the lsn if we add it ? changes are ordered and retrivals are always overridden by the changes if any race. Do we still need lsn ?

> Evictions: emit synthetic ‘change’ with removedFrom=[qid] for the evicted doc (so downstream applies one uniform path).

That is an interesting question, but I think no, adding qid-docid array evictions to the match event could be better, just for compactness

> It must know all active filter predicates to compute membership deltas per event. LMDB is the store; filter evaluation determines add/remove/keep for each connection.

the LMDB is the store of only the documentId-queryId-connectionId relationship and its aggregate documentId-connectionId=numberOfRelationship, the idea is that the query (the filter query) is notified by a change in its range, a document is entering / leaving that range, and makes a change on  documentId-queryId-connectionId and documentId-connectionId as a result, possibly altering the visiblity of that document to some connection. that is it.

> Coalesce multiple actions for the same conn+doc within a tick to avoid chatter

That is an interesting thing, but I am worried about the buffer size, consider having 100k customers, a reasonable buffer size would be 10k, I think that a good size already, even a smaller buffer size can be ok I guess, the think is to limit the buffer size so when achived just emit don't wait the tick, ok I am not against that idea.

> Keep -1 as transient in-memory marker in the store layer (not LMDB). On retrieval with a -1 mark, discard and clear the mark.

Possible, why not

> For new subscriptions, enumerate up to limit doc ids from the doc index and enqueue into RJ; RJ emits ‘retrieval’ events that pass through the same downstream path. This keeps “next ids” ephemeral and aligns with future filter gating.

that is what I said, actually the retrieval events being retrieval events should be known to the filter layer as well, so when sending to the downstream it encodes this information, as well, retrievals are treated as low priority compared to the in order change events. (if we adopt the buffer suggestion we will dedup them prioritizing the last change before even the client notices) 

> Evictions are emitted by the index operator as events (so downstream is uniform), right?

I don't understand what do mean exactly by eviction, if you mean leaving the limit range (please confirm) then yes of course, the index layer tells its downstream that that change

> The filter layer will always recompute per-connection membership on each event (not blindly forward), correct?

wdym recompute per-connection membership ? the filter layer gives new addedTo removedFrom for the previous addedTo removedFrom, it takes each index query children which are filter queries and test if the addedTo query child needs to be notified by addition or not (test the new field against the child predicate) and if the removedFrom query child needs to be notified by the deletion (test the old field against the child predicate). We have a problem here: what about the index queries that match both new and old ? their children may need to add/remove a document since each filter query has its own predicate. how would we deal with this ? One solution maybe to remove the whole lmdb thing, and rely solely on the match event which may look like this: {id,old,new,matchesOld,matchesNew}, apply the filter query predicates to get the same but with query filters references. and then get the queries connections, and notify them. The retrivals are similar : the schema is Map<documentId, {new,indexQueryIds}>, then again match against each index query child (the filter queries). the problem here is in the processing required for checking against all child queries that are in range. we need just this information some relevent filter queries match old or some relevent filter queries match new, for that we can organize the index query children in a tree approach so the disjuction doesn't need to computed thouroughly. Do you think this is better ? removing the LMDB and adopting per index query a sub tree of related filter queries ?




I said the evictions should be a different field, because it is not just queryIds, but a Map<QueryId, DocumentId>
For keeping the LMDB, I see it makes sense, because when organizing filters in a tree we can ignore branches that are checked for both old and new, and will be no need therefore to parse the two branches recollecting the connections etc, ignoring those branches and using the synced LMDB should save a lot of work




{x: 1, y: 4}
{x: 3, y: -3}

{x > 0, y > 0}
{x > 0, y < 0}
{x < 0, y > 0}
{x < 0, y < 0}
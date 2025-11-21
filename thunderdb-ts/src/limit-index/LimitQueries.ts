import { DocId, QueryId } from "./types";
import { DocsTreap } from "./docs-index.ts/docs-index.treap";
import { QueriesTreap } from "./queries-index/queries-index.treap";


interface QueryInfo { id: QueryId; a: number; k: bigint; max: number; }

export class DynamicRangeQueries {
    private docs = new DocsTreap();
    private queries = new QueriesTreap();
    private nextId: QueryId = 1n;
    private idToQuery: Map<QueryId, QueryInfo> = new Map();
    // baseScore stored at insertion for fast removal
    private idToBaseScore: Map<QueryId, bigint> = new Map();

    addDocument(value: number, id: DocId): void {
        this.docs.add(value, id);
        // All queries with a > value increase their score by delta
        this.queries.rangeAddKeysGreaterThan(value, 1n);
    }
    removeDocument(value: number, id: DocId): void {
        this.docs.remove(value, id);
        // All queries with a > value increase their score by delta
        this.queries.rangeAddKeysGreaterThan(value, -1n);
    }

    // Add a query (a=minValue, k=numDocs, max=upper bound on value). Returns query id.
    addQuery(a: number, k: bigint, max = Number.POSITIVE_INFINITY): QueryId {
        const id = this.nextId++;
        const effectiveScore = this.docs.rank(a) + k;
        this.queries.insert(a, id, effectiveScore, max);
        // We need to store baseScore used at the node for deletion. Compute it by re-deriving via a targeted lookup.
        // Easiest: store as effectiveScore minus current accumulated add at position a.
        // We can compute accumulated add at position a by walking the treap without modifying it.
        const baseScore = this.getBaseScoreAtKeyForValue(a, effectiveScore);
        this.idToBaseScore.set(id, baseScore);
        this.idToQuery.set(id, { id, a, k, max });
        return id;
    }

    // Internal: compute baseScore = effectiveScore - accumulatedAddAtPosition(a)
    private getBaseScoreAtKeyForValue(a: number, effectiveScore: bigint): bigint {
        let n = this.queries.root;
        let accAdd = 0n;
        while (n) {
            if (a === n.key) {
                accAdd += n.add;
                break;
            }
            accAdd += n.add;
            n = (a < n.key) ? n.l : n.r;
        }
        return effectiveScore - accAdd;
    }

    // Remove a query by id. Returns true if removed.
    removeQuery(id: QueryId): boolean {
        const info = this.idToQuery.get(id);
        if (!info) return false;
        const baseScore = this.idToBaseScore.get(id);
        if (baseScore === undefined) return false;
        this.queries.remove(info.a, id, baseScore, info.max);
        this.idToBaseScore.delete(id);
        this.idToQuery.delete(id);
        return true;
    }

    // Retrieve all queries (ids) that currently cover value v.
    // If you want full (a,k), map over ids via getQueryInfo.
    getQueriesCovering(v: number): QueryId[] {
        const cutoff = this.docs.rank(v);
        const out: QueryId[] = [];
        this.queries.collectForValue(
            v,
            cutoff,
            (id) => {
                const qi = this.idToQuery.get(id);
                return !!qi && qi.max >= v;
            },
            (id) => out.push(id)
        );
        return out;
    }

    getQueryInfo(id: QueryId): QueryInfo | undefined { return this.idToQuery.get(id); }
}


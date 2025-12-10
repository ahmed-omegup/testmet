import { strict as assert } from "node:assert";
import { DocId, QueryId, Score } from "./types";
import { DocsTreap } from "./docs-index.ts/docs-index.treap";
import { QueriesTreap } from "./queries-index/queries-index.treap";


interface QueryInfo { id: QueryId; a: Score; k: bigint; max: Score; currentMatches: bigint; }

interface AddResult {
    matched: QueryId[];
    blocked: QueryId[];
}

const min = (a: bigint, b: bigint) => a < b ? a : b;
const CHECK_INVARIANTS = process.env.LIMIT_CHECK_INVARIANTS === '1';
const DEBUG_DOC_ID = process.env.LIMIT_DEBUG_DOC ? (BigInt(process.env.LIMIT_DEBUG_DOC) as DocId) : null;
const DEBUG_QUERY_ID = process.env.LIMIT_DEBUG_QUERY ? (BigInt(process.env.LIMIT_DEBUG_QUERY) as QueryId) : null;

export class DynamicRangeQueries {
    private docs = new DocsTreap();
    private queries = new QueriesTreap();
    private nextId: QueryId = 1n;
    private idToQuery: Map<QueryId, QueryInfo> = new Map();
    // baseScore stored at insertion for fast removal
    private idToBaseScore: Map<QueryId, bigint> = new Map();

    private verifyCurrentMatches(context: string): void {
        if (!CHECK_INVARIANTS) return;
        for (const q of this.idToQuery.values()) {
            const actual = min(this.countDocsInRange(q.a, q.max), q.k);
            if (actual !== q.currentMatches) {
                const sampleDocs = this.docs.collectRange(q.a, q.max, q.k);
                this.debugQueryEvent(`mismatch context=${context} actual=${actual.toString()}`, q);
                throw new Error(`[${context}] currentMatches mismatch for query ${q.id.toString()} range=[${q.a},${q.max}] limit=${q.k.toString()} current=${q.currentMatches.toString()} actual=${actual.toString()} sampleDocs=${sampleDocs.map(id => id.toString()).join(',')}`);
            }
        }
    }

    private verifySingleQuery(q: QueryInfo, context: string): void {
        if (!CHECK_INVARIANTS) return;
        const actual = min(this.countDocsInRange(q.a, q.max), q.k);
        if (actual !== q.currentMatches) {
            const sampleDocs = this.docs.collectRange(q.a, q.max, q.k);
            this.debugQueryEvent(`single mismatch context=${context} actual=${actual.toString()}`, q);
            throw new Error(`[${context}] currentMatches mismatch for query ${q.id.toString()} range=[${q.a},${q.max}] limit=${q.k.toString()} current=${q.currentMatches.toString()} actual=${actual.toString()} sampleDocs=${sampleDocs.map(id => id.toString()).join(',')}`);
        }
    }

    private describeQuery(q: QueryInfo): Record<string, string> {
        const sampleDocs = this.docs.collectRange(q.a, q.max, q.k);
        const actual = this.countDocsInRange(q.a, q.max);
        return {
            queryId: q.id.toString(),
            currentMatches: q.currentMatches.toString(),
            limit: q.k.toString(),
            actualDocsInRange: actual.toString(),
            sampleDocs: sampleDocs.map(id => id.toString()).join(','),
            range: `[${q.a},${q.max}]`,
        };
    }

    private debugQueryEvent(action: string, q: QueryInfo): void {
        if (!CHECK_INVARIANTS || DEBUG_QUERY_ID === null || q.id !== DEBUG_QUERY_ID) return;
        console.error(`[debug query ${action}]`, this.describeQuery(q));
    }

    private accumulatedAddAtKey(a: Score): bigint {
        return this.queries.accumulatedAddAtKey(a);
    }

    private describeTreapEntry(id: QueryId): Record<string, string> | null {
        const info = this.idToQuery.get(id);
        if (!info) return null;
        const base = this.idToBaseScore.get(id);
        if (base === undefined) return null;
        const acc = this.accumulatedAddAtKey(info.a);
        const effective = base + acc;
        return {
            baseScore: base.toString(),
            accumulatedAdd: acc.toString(),
            effectiveScore: effective.toString(),
        };
    }

    private scanQueriesForValue(value: Score, docId: DocId | null): QueryInfo[] {
        const matches: QueryInfo[] = [];
        const docRank = this.docs.rank(value, docId);
        for (const q of this.idToQuery.values()) {
            if (value < q.a || value > q.max) continue;
            const startRank = this.docs.rank(q.a, null);
            const distance = docRank - startRank;
            if (distance >= 0n && distance < q.k) {
                matches.push(q);
            }
        }
        return matches;
    }

    private verifyCoveringConsistency(value: Score, docId: DocId | null, actual: QueryInfo[]): void {
        if (!CHECK_INVARIANTS) return;
        const expected = this.scanQueriesForValue(value, docId);
        const toIdSet = (items: QueryInfo[]) => new Set(items.map(q => q.id.toString()));
        const expectedSet = toIdSet(expected);
        const actualSet = toIdSet(actual);
        const missing: string[] = [];
        for (const id of expectedSet) {
            if (!actualSet.has(id)) missing.push(id);
        }
        const extra: string[] = [];
        for (const id of actualSet) {
            if (!expectedSet.has(id)) extra.push(id);
        }
        if (missing.length || extra.length) {
            const maybeLogQuery = (label: string) => {
                if (DEBUG_QUERY_ID === null) return;
                const q = this.idToQuery.get(DEBUG_QUERY_ID);
                if (!q) return;
                const docRank = this.docs.rank(value, docId);
                const startRank = this.docs.rank(q.a, null);
                const treapInfo = this.describeTreapEntry(DEBUG_QUERY_ID);
                console.error(`[debug coverage ${label}]`, {
                    queryId: q.id.toString(),
                    value,
                    docId: docId ? docId.toString() : null,
                    startRank: startRank.toString(),
                    docRank: docRank.toString(),
                    distance: (docRank - startRank).toString(),
                    limit: q.k.toString(),
                    max: q.max,
                    currentMatches: q.currentMatches.toString(),
                    describe: this.describeQuery(q),
                    treapInfo,
                });
            };
            if (DEBUG_QUERY_ID !== null && missing.includes(DEBUG_QUERY_ID.toString())) {
                maybeLogQuery('missing');
            }
            if (DEBUG_QUERY_ID !== null && extra.includes(DEBUG_QUERY_ID.toString())) {
                maybeLogQuery('extra');
            }
            throw new Error(`[collectQueriesForValue] inconsistent coverage for value=${value} docId=${docId ? docId.toString() : 'null'} missing=${missing.join(',')} extra=${extra.join(',')}`);
        }
    }

    addDocument(value: Score, id: DocId): AddResult {
        const affected = this.collectQueriesForValue(value, id);
        this.docs.add(value, id);
        this.queries.rangeAddKeysGreaterThan(value, 1n);

        if (CHECK_INVARIANTS && DEBUG_DOC_ID !== null && id === DEBUG_DOC_ID) {
            const expectedIds = this.scanQueriesForValue(value, id).map(q => q.id.toString());
            const actualIds = affected.map(q => q.id.toString());
            const debugQuery = DEBUG_QUERY_ID ? this.idToQuery.get(DEBUG_QUERY_ID) : undefined;
            let debugMetrics: Record<string, string> | undefined;
            if (debugQuery) {
                const startRank = this.docs.rank(debugQuery.a, null);
                const docRank = this.docs.rank(value, id);
                const distance = docRank - startRank;
                debugMetrics = {
                    queryId: debugQuery.id.toString(),
                    startRank: startRank.toString(),
                    docRank: docRank.toString(),
                    distance: distance.toString(),
                    limit: debugQuery.k.toString(),
                    currentMatches: debugQuery.currentMatches.toString(),
                };
            }
            console.error('[debug addDocument]', {
                docId: id.toString(),
                value,
                expectedIds,
                actualIds,
                debugMetrics,
            });
        }

        const matched: QueryId[] = affected.map(q => q.id);
        const blocked: QueryId[] = [];

        for (const q of affected) {
            if (q.currentMatches < q.k) {
                q.currentMatches += 1n;
                this.debugQueryEvent(`increment doc=${id.toString()} value=${value}`, q);
            } else {
                blocked.push(q.id);
                this.debugQueryEvent(`blocked doc=${id.toString()} value=${value}`, q);
            }
        }

        return { matched, blocked };
    }

    removeDocument(value: Score, id: DocId): QueryId[] {
        const affected = this.collectQueriesForValue(value, id);
        this.docs.remove(value, id);
        this.queries.rangeAddKeysGreaterThan(value, -1n);
        affected.forEach(q => {
            if (q.currentMatches <= 0n) throw new Error('Inconsistent query state detected when removing document');
            q.currentMatches--
            this.debugQueryEvent(`decrement doc=${id.toString()} value=${value}`, q);
        });
        return affected.map(q => q.id);
    }

    // Add a query (a=minValue, k=numDocs, max=upper bound on value). Returns query id.
    addQuery(a: Score, k: bigint, max = Number.POSITIVE_INFINITY): QueryId {
        const id = this.nextId++;
        const effectiveScore = this.docs.rank(a, null) + k;
        this.queries.insert(a, id, effectiveScore, max);
        // We need to store baseScore used at the node for deletion. Compute it by re-deriving via a targeted lookup.
        // Easiest: store as effectiveScore minus current accumulated add at position a.
        // We can compute accumulated add at position a by walking the treap without modifying it.
        const baseScore = this.getBaseScoreAtKeyForValue(a, effectiveScore);
        this.idToBaseScore.set(id, baseScore);
        const currentMatches = min(this.countDocsInRange(a, max), k);
        this.idToQuery.set(id, { id, a, k, max, currentMatches });
        return id;
    }

    // Internal: compute baseScore = effectiveScore - accumulatedAddAtPosition(a)
    private getBaseScoreAtKeyForValue(a: Score, effectiveScore: bigint): bigint {
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

    debugVerifyState(context: string): void {
        this.verifyCurrentMatches(context);
    }

    // Retrieve all queries (ids) that currently cover value v.
    // If you want full (a,k), map over ids via getQueryInfo.
    getQueriesCovering(v: Score, docId: DocId | null): QueryId[] {
        return this.collectQueriesForValue(v, docId).map(q => q.id);
    }

    getQueriesCoveringButNot(
        includeValue: Score,
        includeDocId: DocId | null,
        excludeValue: Score,
        excludeDocId: DocId | null
    ): QueryId[] {
        return this.collectQueriesForDifference(includeValue, includeDocId, excludeValue, excludeDocId).map(q => q.id);
    }

    getQueryInfo(id: QueryId): QueryInfo | undefined { return this.idToQuery.get(id); }

    getDocsForQuery(id: QueryId): DocId[] {
        const info = this.idToQuery.get(id);
        if (!info) return [];
        return this.docs.collectRange(info.a, info.max, info.k);
    }

    seedDocuments(entries: Array<{ id: DocId; score: Score }>): void {
        for (const { id, score } of entries) {
            this.docs.add(score, id);
        }
    }

    private collectQueriesForValue(v: Score, docId: DocId | null): QueryInfo[] {
        const cutoff = this.docs.rank(v, docId);
        const out: QueryInfo[] = [];
        const debugConfig = (CHECK_INVARIANTS && DEBUG_QUERY_ID !== null) ? {
            queryId: DEBUG_QUERY_ID,
            onPrune: (info: Record<string, unknown>) => console.error('[debug collect prune]', info),
        } : undefined;
        this.queries.collectForValue(
            v,
            cutoff,
            (id) => {
                const qi = this.idToQuery.get(id);
                return !!qi && qi.max >= v;
            },
            (id) => {
                const qi = this.idToQuery.get(id);
                if (qi) out.push(qi);
            },
            debugConfig
        );
        this.verifyCoveringConsistency(v, docId, out);
        return out;
    }

    private collectQueriesForDifference(
        includeValue: Score,
        includeDocId: DocId | null,
        excludeValue: Score,
        excludeDocId: DocId | null
    ): QueryInfo[] {
        const includeCutoff = this.docs.rank(includeValue, includeDocId);
        const excludeCutoff = this.docs.rank(excludeValue, excludeDocId);
        const out: QueryInfo[] = [];
        const debugConfig = (CHECK_INVARIANTS && DEBUG_QUERY_ID !== null) ? {
            queryId: DEBUG_QUERY_ID,
            onPrune: (info: Record<string, unknown>) => console.error('[debug collect diff prune]', info),
        } : undefined;
        this.queries.collectDifferenceForValue(
            includeValue,
            includeCutoff,
            excludeValue,
            excludeCutoff,
            (id) => {
                const qi = this.idToQuery.get(id);
                return !!qi && qi.max >= includeValue;
            },
            (id) => {
                const qi = this.idToQuery.get(id);
                return !!qi && qi.max >= excludeValue;
            },
            (id) => {
                const qi = this.idToQuery.get(id);
                if (qi) out.push(qi);
            },
            debugConfig
        );
        return out;
    }

    private countDocsInRange(min: Score, max: Score): bigint {
        const upper = this.docs.countAtMost(max);
        const lower = this.docs.rank(min, null);
        const diff = upper - lower;
        return diff < 0n ? 0n : diff;
    }

    pickOverflowDoc(id: QueryId): DocId | null {
        const info = this.idToQuery.get(id);
        if (!info) return null;
        if (info.currentMatches < info.k) return null;
        return this.docForQueryAt(info, info.k);
    }

    fillGap(id: QueryId): DocId | null {
        const info = this.idToQuery.get(id);
        if (!info) return null;
        if (info.currentMatches >= info.k) return null;
        this.debugQueryEvent(`fillGap attempt query=${id.toString()}`, info);
        const doc = this.docForQueryAt(info, info.currentMatches);
        if (!doc) {
            this.debugQueryEvent(`fillGap miss query=${id.toString()}`, info);
            return null;
        }
        info.currentMatches += 1n;
        this.debugQueryEvent(`fillGap query=${id.toString()}`, info);
        this.verifySingleQuery(info, `fillGap query=${id.toString()}`);
        return doc;
    }

    private docForQueryAt(info: QueryInfo, offset: bigint): DocId | null {
        if (offset < 0n) return null;
        const startRank = this.docs.rank(info.a, null);
        const tuple = this.docs.getAtRank(startRank + offset);
        if (!tuple) return null;
        const [score, id, position] = tuple;
        if (score > info.max) return null;
        const index = Number(position);
        assert(Number.isSafeInteger(index), 'doc index exceeds safe integer range');
        return id ?? null;
    }

}


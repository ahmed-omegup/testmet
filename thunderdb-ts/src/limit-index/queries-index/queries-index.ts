import { QueryId } from "../types"

export interface CollectDebugConfig {
    queryId: QueryId;
    onPrune: (info: Record<string, unknown>) => void;
}

export interface QueriesIndex {
    rangeAddKeysGreaterThan(t: number, delta: bigint): void
    insert(a: number, id: QueryId, effectiveScore: bigint, maxCap: number): void
    remove(a: number, id: QueryId, baseScore: bigint, maxCap: number): void
    collectForValue(v: number, cutoff: bigint, isAllowed: (id: QueryId) => boolean, visit: (id: QueryId) => void, debug?: CollectDebugConfig): void
    collectDifferenceForValue(
        includeValue: number,
        includeCutoff: bigint,
        excludeValue: number,
        excludeCutoff: bigint,
        includeAllowed: (id: QueryId) => boolean,
        excludeAllowed: (id: QueryId) => boolean,
        visit: (id: QueryId) => void,
        debug?: CollectDebugConfig
    ): void
    accumulatedAddAtKey(a: number): bigint
}
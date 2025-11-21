import { QueryId } from "../types"

export interface QueriesIndex {
    rangeAddKeysGreaterThan(t: number, delta: bigint): void
    insert(a: number, id: QueryId, effectiveScore: bigint, maxCap: number): void
    remove(a: number, id: QueryId, baseScore: bigint, maxCap: number): void
    collectForValue(v: number, cutoff: bigint, isAllowed: (id: QueryId) => boolean, visit: (id: QueryId) => void): void
}
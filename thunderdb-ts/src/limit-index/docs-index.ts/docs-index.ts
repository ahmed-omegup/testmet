import { DocId, Score } from "../types";
export type Nullable<T> = T | null;

export interface DocsIndex {
    add(score: Score, id: DocId): void
    remove(score: Score, id: DocId): void
    rank(score: Score): bigint
    countAtMost(score: Score): bigint
    getAtRank(rank: bigint): null | [score: Score, ids: DocId[], position: bigint]
}
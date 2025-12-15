import { StreamItem } from './limit-index/limitStream';
import { DocId, DocStateDom, QueryId, QuerySpec, Score } from './limit-index/types';

export type SocketDocState = DocStateDom & { scoreValue: Score };

export type WireDocState = { scoreValue: number };

export interface WireDocRef {
  id: string;
  state: WireDocState;
}

export type WireDocChange = {
  id: string;
  old: WireDocState | null;
  new: WireDocState | null;
};

export interface WireQuerySpec {
  minScore: number;
  maxScore: number;
  limit: string;
}

export type WireStreamItem =
  | { kind: 'doc-changes'; changes: WireDocChange[] }
  | { kind: 'query-adds'; specs: WireQuerySpec[] }
  | { kind: 'query-removes'; ids: string[] }
  | { kind: 'seed-docs'; docs: WireDocRef[] };

export interface WorkerRunSummary {
  matchEvents: number;
  evictions: number;
  retrievalBatches: number;
  retrievalDocs: number;
  endTs: number;
  startTs: number;
  eventsProcessed: number;
}

export type ClientMessage =
  | { type: 'hello'; role: 'client'; version: 1 }
  | { type: 'event'; item: WireStreamItem }
  | { type: 'end' };

export type ServerMessage =
  | { type: 'hello'; role: 'worker'; version: 1 }
  | { type: 'summary'; summary: WorkerRunSummary }
  | { type: 'error'; message: string };

const toDocId = (value: string): DocId => BigInt(value) as DocId;
export const fromDocId = (value: DocId): string => value.toString();
const toQueryId = (value: string): QueryId => BigInt(value) as QueryId;
const fromQueryId = (value: QueryId): string => value.toString();

const toDocState = (state: WireDocState): SocketDocState => ({ scoreValue: state.scoreValue as Score } as SocketDocState);
const fromDocState = (state: SocketDocState): WireDocState => ({ scoreValue: Number(state.scoreValue) });

let i = 1
const toQuerySpec = (spec: WireQuerySpec): QuerySpec => ({
  minScore: spec.minScore as Score,
  maxScore: spec.maxScore as Score,
  limit: BigInt(spec.limit),
  id: i++,
});


export const wireToStreamItem = (item: WireStreamItem): StreamItem<SocketDocState>[] => {
  switch (item.kind) {
    case 'doc-changes':
      return item.changes.map(change => ({
        kind: 'doc-change',
        change: {
          id: toDocId(change.id),
          old: change.old ? toDocState(change.old) : null,
          new: change.new ? toDocState(change.new) : null,
        },
      }))
    case 'query-adds':
      return item.specs.map(spec => ({
        kind: 'query-add',
        spec: toQuerySpec(spec),
      }));
    case 'query-removes':
      return item.ids.map(id => ({
        kind: 'query-remove',
        id: toQueryId(id),
      }));
    case 'seed-docs':
      return [{
        kind: 'seed-docs',
        docs: item.docs.map(doc => ({
          id: toDocId(doc.id),
          state: toDocState(doc.state),
        })),
      }];
  }
};


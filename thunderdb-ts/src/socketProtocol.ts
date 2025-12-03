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
  | { kind: 'doc-change'; change: WireDocChange }
  | { kind: 'query-add'; spec: WireQuerySpec }
  | { kind: 'query-remove'; id: string }
  | { kind: 'seed-docs'; docs: WireDocRef[] };

export interface WorkerRunSummary {
  matchEvents: number;
  evictions: number;
  retrievalBatches: number;
  retrievalDocs: number;
  endTs: number;
  eventsProcessed: number;
}

export type ClientMessage =
  | { type: 'hello'; role: 'client'; version: 1 }
  | { type: 'event'; item: WireStreamItem }
  | { type: 'event-batch'; items: WireStreamItem[] }
  | { type: 'end' };

export type ServerMessage =
  | { type: 'hello'; role: 'worker'; version: 1 }
  | { type: 'summary'; summary: WorkerRunSummary }
  | { type: 'error'; message: string };

const toDocId = (value: string): DocId => BigInt(value) as DocId;
const fromDocId = (value: DocId): string => value.toString();
const toQueryId = (value: string): QueryId => BigInt(value) as QueryId;
const fromQueryId = (value: QueryId): string => value.toString();

const toDocState = (state: WireDocState): SocketDocState => ({ scoreValue: state.scoreValue as Score } as SocketDocState);
const fromDocState = (state: SocketDocState): WireDocState => ({ scoreValue: Number(state.scoreValue) });

const toQuerySpec = (spec: WireQuerySpec): QuerySpec => ({
  minScore: spec.minScore as Score,
  maxScore: spec.maxScore as Score,
  limit: BigInt(spec.limit),
});

const fromQuerySpec = (spec: QuerySpec): WireQuerySpec => ({
  minScore: Number(spec.minScore),
  maxScore: Number(spec.maxScore),
  limit: spec.limit.toString(),
});

export const wireToStreamItem = (item: WireStreamItem): StreamItem<SocketDocState> => {
  switch (item.kind) {
    case 'doc-change':
      return {
        kind: 'doc-change',
        change: {
          id: toDocId(item.change.id),
          old: item.change.old ? toDocState(item.change.old) : null,
          new: item.change.new ? toDocState(item.change.new) : null,
        },
      };
    case 'query-add':
      return {
        kind: 'query-add',
        spec: toQuerySpec(item.spec),
      };
    case 'query-remove':
      return {
        kind: 'query-remove',
        id: toQueryId(item.id),
      };
    case 'seed-docs':
      return {
        kind: 'seed-docs',
        docs: item.docs.map(doc => ({
          id: toDocId(doc.id),
          state: toDocState(doc.state),
        })),
      };
  }
};

export const streamItemToWire = (item: StreamItem<SocketDocState>): WireStreamItem => {
  switch (item.kind) {
    case 'doc-change':
      return {
        kind: 'doc-change',
        change: {
          id: fromDocId(item.change.id),
          old: item.change.old ? fromDocState(item.change.old) : null,
          new: item.change.new ? fromDocState(item.change.new) : null,
        },
      };
    case 'query-add':
      return {
        kind: 'query-add',
        spec: fromQuerySpec(item.spec),
      };
    case 'query-remove':
      return {
        kind: 'query-remove',
        id: fromQueryId(item.id),
      };
    case 'seed-docs':
      return {
        kind: 'seed-docs',
        docs: item.docs.map(doc => ({
          id: fromDocId(doc.id),
          state: fromDocState(doc.state),
        })),
      };
  }
};

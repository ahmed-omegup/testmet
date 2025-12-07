import fs from 'node:fs';
import path from 'node:path';
import readline from 'node:readline';

interface LogDocState {
  scoreValue: number;
}

interface LogDocChange {
  id: string | number;
  old: LogDocState | null;
  new: LogDocState | null;
}

interface LogQuerySpec {
  minScore: number;
  maxScore: number;
  limit: string | number;
}

interface SeedDocsEvent {
  kind: 'seed-docs';
  docs: Array<{ id: string | number; state: LogDocState }>;
}

interface DocChangeEvent {
  kind: 'doc-change';
  change: LogDocChange;
}

interface QueryAddEvent {
  kind: 'query-add';
  spec: LogQuerySpec;
}

interface QueryRemoveEvent {
  kind: 'query-remove';
  id: string;
}

type UpstreamEvent = SeedDocsEvent | DocChangeEvent | QueryAddEvent | QueryRemoveEvent;

const formatNumber = (value: number) => value.toLocaleString('en-US');

const parseLimit = (value: string | number): number => (typeof value === 'number' ? value : Number(value));

const toDocIdString = (value: string | number): string => (typeof value === 'string' ? value : value.toString());

interface QueryRecord {
  id: string;
  minScore: number;
  maxScore: number;
  limit: number;
  removed: boolean;
}

interface QueryResultSummary {
  queryId: string;
  minScore: number;
  maxScore: number;
  limit: number;
  docs: Array<{ id: string; score: number }>;
}

async function replayLog(filePath: string): Promise<void> {
  const absolutePath = path.resolve(filePath);
  if (!fs.existsSync(absolutePath)) {
    throw new Error(`Log file not found: ${absolutePath}`);
  }

  const docStates = new Map<string, LogDocState>();
  const queries = new Map<string, QueryRecord>();
  let nextQueryId = 1n;
  let upstreamCount = 0;

  const rl = readline.createInterface({
    input: fs.createReadStream(absolutePath, { encoding: 'utf8' }),
    crlfDelay: Infinity,
  });

  for await (const rawLine of rl) {
    const line = rawLine.trim();
    if (!line.startsWith('<<')) continue;
    const payloadIndex = line.indexOf('{');
    if (payloadIndex === -1) continue;
    const json = line.slice(payloadIndex);
    try {
      const data = JSON.parse(json) as UpstreamEvent;
      upstreamCount += 1;
      handleUpstreamEvent(data, docStates, queries, () => nextQueryId++);
    } catch (err) {
      console.warn(`[replay] failed to parse line: ${line}`);
    }
  }

  const results = buildQuerySummaries(docStates, queries);
  outputReport(results, upstreamCount, docStates.size);
}

function handleUpstreamEvent(
  event: UpstreamEvent,
  docStates: Map<string, LogDocState>,
  queries: Map<string, QueryRecord>,
  nextQueryId: () => bigint
): void {
  switch (event.kind) {
    case 'seed-docs': {
      for (const doc of event.docs) {
        docStates.set(toDocIdString(doc.id), doc.state);
      }
      break;
    }
    case 'doc-change': {
      const id = toDocIdString(event.change.id);
      if (event.change.new) {
        docStates.set(id, event.change.new);
      } else {
        docStates.delete(id);
      }
      break;
    }
    case 'query-add': {
      const id = nextQueryId().toString();
      queries.set(id, {
        id,
        minScore: event.spec.minScore,
        maxScore: event.spec.maxScore,
        limit: parseLimit(event.spec.limit),
        removed: false,
      });
      break;
    }
    case 'query-remove': {
      const record = queries.get(event.id);
      if (record) record.removed = true;
      break;
    }
  }
}

function buildQuerySummaries(
  docStates: Map<string, LogDocState>,
  queries: Map<string, QueryRecord>
): QueryResultSummary[] {
  const sortedDocs = Array.from(docStates.entries())
    .map(([id, state]) => ({ id, score: state.scoreValue }))
    .sort((a, b) => {
      if (a.score !== b.score) return a.score - b.score;
      const aId = BigInt(a.id);
      const bId = BigInt(b.id);
      return aId < bId ? -1 : aId > bId ? 1 : 0;
    });

  const summaries: QueryResultSummary[] = [];
  for (const record of queries.values()) {
    if (record.removed) continue;
    const docs: Array<{ id: string; score: number }> = [];
    for (const doc of sortedDocs) {
      if (doc.score < record.minScore) continue;
      if (doc.score > record.maxScore) break;
      docs.push(doc);
      if (docs.length >= record.limit) break;
    }
    summaries.push({
      queryId: record.id,
      minScore: record.minScore,
      maxScore: record.maxScore,
      limit: record.limit,
      docs,
    });
  }
  return summaries;
}

function outputReport(results: QueryResultSummary[], upstreamCount: number, docCount: number): void {
  console.log(`[replay] processed ${formatNumber(upstreamCount)} upstream entries`);
  console.log(`[replay] final doc count: ${formatNumber(docCount)}\n`);
  for (const result of results) {
    const { queryId, minScore, maxScore, limit, docs } = result;
    const docList = docs.map(doc => `${doc.id} (score=${doc.score})`).join(', ');
    console.log(`Query ${queryId} :: range [${minScore}, ${maxScore}] limit ${limit}`);
    console.log(`  docs (${docs.length}): ${docList || '<none>'}`);
  }
}

const logPath = process.argv[2] ?? 'out.log';

replayLog(logPath).catch(err => {
  console.error('[replay] failed', err);
  process.exit(1);
});

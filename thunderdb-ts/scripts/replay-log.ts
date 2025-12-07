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
  id?: string | number;
}

interface QueryRemoveEvent {
  kind: 'query-remove';
  id: string | number;
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

interface QueryDoc {
  id: string;
  score: number;
}

interface QueryResultSummary {
  queryId: string;
  minScore: number;
  maxScore: number;
  limit: number;
  docs: QueryDoc[];
}

interface RetrievalDoc {
  docId: string | number;
  state?: LogDocState;
  queries: Array<string | number>;
}

interface RetrievalEvent {
  kind: 'retrieval';
  batchNumber?: string | number;
  docs: RetrievalDoc[];
}

type DownstreamEvent = RetrievalEvent;

interface QueryMismatch {
  queryId: string;
  minScore: number;
  maxScore: number;
  limit: number;
  expectedCount: number;
  actualCount: number;
  difference?: {
    actual?: QueryDoc;
    expected?: QueryDoc;
  };
}

interface ComparisonSummary {
  totalQueries: number;
  matchedQueries: number;
  mismatches: QueryMismatch[];
  missingExpected: string[];
  extraExpected: string[];
}

async function replayLog(filePath: string): Promise<void> {
  const absolutePath = path.resolve(filePath);
  if (!fs.existsSync(absolutePath)) {
    throw new Error(`Log file not found: ${absolutePath}`);
  }

  const docStates = new Map<string, LogDocState>();
  const queries = new Map<string, QueryRecord>();
  const expectedQueryDocs = new Map<string, QueryDoc[]>();
  const pendingQueryIds: string[] = [];
  let nextQueryId = 1n;
  let upstreamCount = 0;
  let retrievalCount = 0;

  const rl = readline.createInterface({
    input: fs.createReadStream(absolutePath, { encoding: 'utf8' }),
    crlfDelay: Infinity,
  });

  for await (const rawLine of rl) {
    const line = rawLine.trim();
    if (line.startsWith('<<')) {
      const payloadIndex = line.indexOf('{');
      if (payloadIndex === -1) continue;
      const json = line.slice(payloadIndex);
      try {
        const data = JSON.parse(json) as UpstreamEvent;
        upstreamCount += 1;
        handleUpstreamEvent(
          data,
          docStates,
          queries,
          () => nextQueryId++,
          (id: string) => pendingQueryIds.push(id)
        );
      } catch (err) {
        console.warn(`[replay] failed to parse upstream line: ${line}`);
      }
      continue;
    }
    if (line.startsWith('>>')) {
      const payloadIndex = line.indexOf('{');
      if (payloadIndex === -1) continue;
      const json = line.slice(payloadIndex);
      try {
        const data = JSON.parse(json) as DownstreamEvent;
        if (handleDownstreamEvent(data, expectedQueryDocs, pendingQueryIds)) {
          retrievalCount += 1;
        }
      } catch (err) {
        console.warn(`[replay] failed to parse downstream line: ${line}`);
      }
    }
  }

  const results = buildQuerySummaries(docStates, queries);
  const comparison = compareAgainstExpected(results, expectedQueryDocs);
  outputReport(comparison, upstreamCount, retrievalCount, docStates.size);
}

function handleUpstreamEvent(
  event: UpstreamEvent,
  docStates: Map<string, LogDocState>,
  queries: Map<string, QueryRecord>,
  nextQueryId: () => bigint,
  onQueryAdd?: (id: string) => void
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
      const id = event.id ? toDocIdString(event.id) : nextQueryId().toString();
      queries.set(id, {
        id,
        minScore: event.spec.minScore,
        maxScore: event.spec.maxScore,
        limit: parseLimit(event.spec.limit),
        removed: false,
      });
      if (onQueryAdd) onQueryAdd(id);
      break;
    }
    case 'query-remove': {
      const record = queries.get(toDocIdString(event.id));
      if (record) record.removed = true;
      break;
    }
  }
}

function handleDownstreamEvent(
  event: DownstreamEvent,
  expectedQueryDocs: Map<string, QueryDoc[]>,
  pendingQueryIds: string[]
): boolean {
  if (event.kind !== 'retrieval') return false;
  const queryId = pendingQueryIds.shift();
  if (!queryId) return false;
  const docs = normalizeDocList(
    event.docs.map(doc => ({
      id: toDocIdString(doc.docId),
      score: doc.state?.scoreValue ?? Number.NEGATIVE_INFINITY,
    }))
  );
  expectedQueryDocs.set(queryId, docs);
  return true;
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
    const docs: QueryDoc[] = [];
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

function compareAgainstExpected(
  actualResults: QueryResultSummary[],
  expectedResults: Map<string, QueryDoc[]>
): ComparisonSummary {
  const mismatches: QueryMismatch[] = [];
  const missingExpected: string[] = [];
  let matchedQueries = 0;
  const actualMap = new Map(actualResults.map(result => [result.queryId, result]));

  for (const result of actualResults) {
    const expectedDocs = expectedResults.get(result.queryId);
    if (!expectedDocs) {
      missingExpected.push(result.queryId);
      continue;
    }
    const comparison = compareDocLists(normalizeDocList(result.docs), normalizeDocList(expectedDocs));
    if (comparison.equal) {
      matchedQueries += 1;
    } else {
      mismatches.push({
        queryId: result.queryId,
        minScore: result.minScore,
        maxScore: result.maxScore,
        limit: result.limit,
        expectedCount: expectedDocs.length,
        actualCount: result.docs.length,
        difference: comparison.firstDifference,
      });
    }
  }

  const extraExpected: string[] = [];
  for (const queryId of expectedResults.keys()) {
    if (!actualMap.has(queryId)) {
      extraExpected.push(queryId);
    }
  }

  return {
    totalQueries: actualResults.length,
    matchedQueries,
    mismatches,
    missingExpected,
    extraExpected,
  };
}

function outputReport(
  comparison: ComparisonSummary,
  upstreamCount: number,
  retrievalCount: number,
  docCount: number
): void {
  console.log(`[replay] processed ${formatNumber(upstreamCount)} upstream entries`);
  console.log(`[replay] processed ${formatNumber(retrievalCount)} retrieval batches`);
  console.log(`[replay] final doc count: ${formatNumber(docCount)}`);

  if (comparison.totalQueries === 0) {
    console.log('[replay] no active queries to validate.');
    return;
  }

  const mismatchTotal = comparison.mismatches.length + comparison.missingExpected.length;
  if (mismatchTotal === 0) {
    console.log(
      `[replay] ✅ Final state matches downstream retrievals for ${formatNumber(comparison.totalQueries)} queries.`
    );
    return;
  }

  console.error(
    `[replay] ❌ Final state mismatch. matched=${formatNumber(comparison.matchedQueries)} / ${formatNumber(
      comparison.totalQueries
    )}, mismatched=${formatNumber(comparison.mismatches.length)}, missing=${formatNumber(
      comparison.missingExpected.length
    )}`
  );

  for (const mismatch of comparison.mismatches.slice(0, 5)) {
    const diffParts: string[] = [];
    if (mismatch.difference?.expected) diffParts.push(`expected ${describeDoc(mismatch.difference.expected)}`);
    if (mismatch.difference?.actual) diffParts.push(`actual ${describeDoc(mismatch.difference.actual)}`);
    console.error(
      `[replay] query ${mismatch.queryId} range [${mismatch.minScore}, ${mismatch.maxScore}] limit ${mismatch.limit} mismatch (${diffParts.join(
        ' vs '
      ) || 'counts differ'})`
    );
  }
  if (comparison.mismatches.length > 5) {
    console.error(`[replay] ... ${comparison.mismatches.length - 5} more mismatched queries`);
  }
  if (comparison.missingExpected.length) {
    console.error(`[replay] missing downstream retrievals for queries: ${comparison.missingExpected.join(', ')}`);
  }
  if (comparison.extraExpected.length) {
    console.error(`[replay] downstream retrievals without active queries: ${comparison.extraExpected.join(', ')}`);
  }
}

function normalizeDocList(docs: QueryDoc[]): QueryDoc[] {
  return [...docs].sort((a, b) => {
    if (a.score !== b.score) return a.score - b.score;
    try {
      const aId = BigInt(a.id);
      const bId = BigInt(b.id);
      if (aId < bId) return -1;
      if (aId > bId) return 1;
      return 0;
    } catch {
      return a.id.localeCompare(b.id);
    }
  });
}

function compareDocLists(
  actual: QueryDoc[],
  expected: QueryDoc[]
): { equal: boolean; firstDifference?: { actual?: QueryDoc; expected?: QueryDoc } } {
  const maxLen = Math.max(actual.length, expected.length);
  for (let i = 0; i < maxLen; i += 1) {
    const actualDoc = actual[i];
    const expectedDoc = expected[i];
    if (!actualDoc || !expectedDoc) {
      return { equal: false, firstDifference: { actual: actualDoc, expected: expectedDoc } };
    }
    if (actualDoc.id !== expectedDoc.id || actualDoc.score !== expectedDoc.score) {
      return { equal: false, firstDifference: { actual: actualDoc, expected: expectedDoc } };
    }
  }
  return { equal: true };
}

function describeDoc(doc?: QueryDoc): string {
  if (!doc) return '<none>';
  return `${doc.id} (score=${doc.score})`;
}

const logPath = process.argv[2] ?? 'out.log';

replayLog(logPath).catch(err => {
  console.error('[replay] failed', err);
  process.exit(1);
});

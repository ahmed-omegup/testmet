import dotenv from 'dotenv';
import net from 'node:net';
import readline from 'node:readline';
import { performance } from 'node:perf_hooks';
import { runLimitStreamAsync } from './limit-index/limitStream';
import { DownstreamEvent } from './limit-index/types';
import { RetrievalJobWorker } from './retrievalJob';
import { LmdbDocStore, LmdbDurability } from './docStore';
import {
  ClientMessage,
  ServerMessage,
  SocketDocState,
  WorkerRunConfig,
  WorkerRunSummary,
  wireToStreamItem,
} from './socketProtocol';

dotenv.config();

const PROTOCOL_VERSION = 1;
const DEFAULT_PORT = Number(process.env.WORKER_PORT ?? 4040);
const DEFAULT_HOST = process.env.WORKER_HOST ?? '0.0.0.0';
const DOCSTORE_DURABILITY: LmdbDurability = process.env.THUNDERDB_DOCSTORE_DURABILITY === 'relaxed' ? 'relaxed' : 'durable';
const WORKER_PROGRESS_STEP = Math.max(1, Number(process.env.WORKER_PROGRESS_STEP ?? 10000));
const formatNumber = (value: number) => value.toLocaleString('en-US');

type RunState = {
  queue: AsyncStreamQueue;
  docStore?: LmdbDocStore<SocketDocState>;
  retrievalJob?: RetrievalJobWorker<SocketDocState>;
  matchEvents: number;
  evictions: number;
  retrievalBatches: number;
  retrievalDocs: number;
  eventsProcessed: number;
  startTime: number;
};

class AsyncStreamQueue {
  private buffer: SocketStreamItem[] = [];
  private waiting: Array<() => void> = [];
  private closed = false;

  push(item: SocketStreamItem): void {
    if (this.closed) throw new Error('queue already closed');
    this.buffer.push(item);
    this.flush();
  }

  close(): void {
    if (this.closed) return;
    this.closed = true;
    this.flush();
  }

  async *consume(): AsyncIterableIterator<SocketStreamItem> {
    while (true) {
      if (this.buffer.length) {
        yield this.buffer.shift()!;
        continue;
      }
      if (this.closed) break;
      await new Promise<void>(resolve => this.waiting.push(resolve));
    }
  }

  private flush(): void {
    const waiter = this.waiting.shift();
    if (waiter) waiter();
  }
}

type SocketStreamItem = ReturnType<typeof wireToStreamItem>;

const getScore = (state: SocketDocState) => state.scoreValue;

const createRunState = (config: WorkerRunConfig): RunState => {
  const queue = new AsyncStreamQueue();
  const runState: RunState = {
    queue,
    matchEvents: 0,
    evictions: 0,
    retrievalBatches: 0,
    retrievalDocs: 0,
    eventsProcessed: 0,
    startTime: performance.now(),
  };
  if (config.enableRetrieval) {
    runState.docStore = new LmdbDocStore<SocketDocState>({ durability: DOCSTORE_DURABILITY });
    runState.retrievalJob = new RetrievalJobWorker<SocketDocState>(
      ids => runState.docStore!.getMany(ids),
      event => {
        runState.retrievalBatches += 1;
        runState.retrievalDocs += event.docs.length;
      }
    );
  }
  return runState;
};

const buildSummary = (state: RunState, durationMs: number): WorkerRunSummary => ({
  durationMs,
  eventsProcessed: state.eventsProcessed,
  matchEvents: state.matchEvents,
  evictions: state.evictions,
  retrievalBatches: state.retrievalBatches,
  retrievalDocs: state.retrievalDocs,
});

const handleDownstreamEvent = (state: RunState, event: DownstreamEvent<SocketDocState>) => {
  if (event.kind === 'match') {
    state.matchEvents += 1;
    state.evictions += event.evictions.length;
    return;
  }
  state.retrievalBatches += 1;
  state.retrievalDocs += event.docs.length;
};

const logWorkerProgressIfNeeded = (state: RunState): void => {
  if (state.eventsProcessed === 0) return;
  if (state.eventsProcessed % WORKER_PROGRESS_STEP === 0) {
    console.log(`[worker] processed ${formatNumber(state.eventsProcessed)} events`);
  }
};

const sendMessage = (socket: net.Socket, message: ServerMessage): void => {
  socket.write(`${JSON.stringify(message)}\n`);
};

const startServer = () => {
  const server = net.createServer(socket => {
    const rl = readline.createInterface({ input: socket, crlfDelay: Infinity });
    let handshakeComplete = false;
    let runState: RunState | null = null;
    let runPromise: Promise<WorkerRunSummary> | null = null;
    let closing = false;

    const cleanup = async () => {
      if (closing) return;
      closing = true;
      rl.close();
      socket.destroy();
      if (runState?.retrievalJob) await runState.retrievalJob.stop().catch(() => undefined);
    };

    rl.on('line', async line => {
      let payload: ClientMessage;
      try {
        payload = JSON.parse(line) as ClientMessage;
      } catch (err) {
        sendMessage(socket, { type: 'error', message: 'invalid json' });
        return;
      }

      if (payload.type === 'hello') {
        if (handshakeComplete) {
          sendMessage(socket, { type: 'error', message: 'duplicate hello' });
          return;
        }
        if (payload.version !== PROTOCOL_VERSION) {
          sendMessage(socket, { type: 'error', message: 'protocol version mismatch' });
          await cleanup();
          return;
        }
        handshakeComplete = true;
        sendMessage(socket, { type: 'hello', role: 'worker', version: PROTOCOL_VERSION });
        return;
      }

      if (!handshakeComplete) {
        sendMessage(socket, { type: 'error', message: 'handshake required' });
        return;
      }

      switch (payload.type) {
        case 'run': {
          if (runPromise) {
            sendMessage(socket, { type: 'error', message: 'run already in progress' });
            return;
          }
          runState = createRunState(payload.config);
          const localState = runState;
          runPromise = (async () => {
            try {
              await runLimitStreamAsync(localState.queue.consume(), getScore, event => handleDownstreamEvent(localState, event), {
                retrievalJob: localState.retrievalJob,
                docStore: localState.docStore,
              });
              console.log('[worker] run completed', performance.now() - localState.startTime);
              if (localState.retrievalJob) {
                await localState.retrievalJob.stop();
              }
              console.log('[worker] retrieval job stopped', performance.now() - localState.startTime);
              const durationMs = performance.now() - localState.startTime;
              return buildSummary(localState, durationMs);
            } finally {
              localState.queue.close();
            }
          })();
          sendMessage(socket, { type: 'run-accepted' });
          break;
        }
        case 'event': {
          if (!runState) {
            sendMessage(socket, { type: 'error', message: 'no active run' });
            return;
          }
          try {
            const item = wireToStreamItem(payload.item);
            runState.queue.push(item);
            runState.eventsProcessed += 1;
            logWorkerProgressIfNeeded(runState);
          } catch (err) {
            sendMessage(socket, { type: 'error', message: 'failed to ingest event' });
          }
          break;
        }
        case 'event-batch': {
          if (!runState) {
            sendMessage(socket, { type: 'error', message: 'no active run' });
            return;
          }
          if (!Array.isArray(payload.items) || payload.items.length === 0) {
            sendMessage(socket, { type: 'error', message: 'empty event batch' });
            return;
          }
          console.log('event-batch received', payload.items.length);
          try {
            for (const wireItem of payload.items) {
              const item = wireToStreamItem(wireItem);
              runState.queue.push(item);
              runState.eventsProcessed += 1;
              logWorkerProgressIfNeeded(runState);
            }
          } catch (err) {
            sendMessage(socket, { type: 'error', message: 'failed to ingest batch' });
          }
          break;
        }
        case 'end': {
          console.log('[worker] received end of stream');
          if (!runPromise || !runState) {
            sendMessage(socket, { type: 'error', message: 'no active run' });
            return;
          }
          runState.queue.close();
          try {
            const summary = await runPromise;
            sendMessage(socket, { type: 'summary', summary });
          } catch (err) {
            sendMessage(socket, { type: 'error', message: err instanceof Error ? err.message : 'run failed' });
          } finally {
            runPromise = null;
            runState = null;
          }
          break;
        }
        default:
          sendMessage(socket, { type: 'error', message: 'unknown message type' });
      }
    });

    socket.on('close', async () => {
      if (runState) {
        runState.queue.close();
      }
      await cleanup();
    });

    socket.on('error', async () => {
      if (runState) {
        runState.queue.close();
      }
      await cleanup();
    });
  });

  server.listen(DEFAULT_PORT, DEFAULT_HOST, () => {
    console.log(`[worker] listening on ${DEFAULT_HOST}:${DEFAULT_PORT}`);
  });
};

startServer();

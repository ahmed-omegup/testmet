import dotenv from 'dotenv';
import net from 'node:net';
import readline from 'node:readline';
import { LmdbDurability } from './docStore';
import { ClientMessage, ServerMessage, wireToStreamItem } from './socketProtocol';
import { WorkerRuntime } from './workerRuntime';

dotenv.config();

const PROTOCOL_VERSION = 1;
const DEFAULT_PORT = Number(process.env.WORKER_PORT ?? 4040);
const DEFAULT_HOST = process.env.WORKER_HOST ?? '0.0.0.0';
const DOCSTORE_DURABILITY: LmdbDurability = process.env.THUNDERDB_DOCSTORE_DURABILITY === 'relaxed' ? 'relaxed' : 'durable';
const WORKER_PROGRESS_STEP = Math.max(1, Number(process.env.WORKER_PROGRESS_STEP ?? 10000));

type LineHandler = (line: string) => void;
type VoidHandler = () => void;
type ErrorHandler = (error: Error) => void;

export interface LineTransport {
  send(line: string): void;
  onLine(handler: LineHandler): void;
  onClose(handler: VoidHandler): void;
  onError(handler: ErrorHandler): void;
  close(): void;
}

export const createSocketTransport = (socket: net.Socket): LineTransport => {
  const rl = readline.createInterface({ input: socket, crlfDelay: Infinity });
  const lineHandlers: LineHandler[] = [];
  const closeHandlers: VoidHandler[] = [];
  const errorHandlers: ErrorHandler[] = [];

  rl.on('line', line => {
    for (const handler of lineHandlers) handler(line);
  });

  socket.on('close', () => {
    for (const handler of closeHandlers) handler();
  });

  socket.on('error', err => {
    for (const handler of errorHandlers) handler(err);
  });

  return {
    send(line: string) {
      socket.write(`${line}\n`);
    },
    onLine(handler: LineHandler) {
      lineHandlers.push(handler);
    },
    onClose(handler: VoidHandler) {
      closeHandlers.push(handler);
    },
    onError(handler: ErrorHandler) {
      errorHandlers.push(handler);
    },
    close() {
      rl.close();
      socket.end();
      socket.destroy();
    },
  };
};

const sendMessage = (transport: LineTransport, message: ServerMessage): void => {
  transport.send(JSON.stringify(message));
};

export const handleTransport = (transport: LineTransport) => {
  let handshakeComplete = false;
  let closing = false;
  const runtime = new WorkerRuntime({
    docStoreDurability: DOCSTORE_DURABILITY,
    progressStep: WORKER_PROGRESS_STEP,
    log: message => console.log(message),
  });

  const cleanup = async (closeTransport = false) => {
    if (closing) return;
    closing = true;
    runtime.abortRun();
    if (closeTransport) transport.close();
  };

  transport.onLine(async line => {
      let payload: ClientMessage;
      try {
        payload = JSON.parse(line) as ClientMessage;
      } catch (err) {
        sendMessage(transport, { type: 'error', message: 'invalid json' });
        return;
      }

      if (payload.type === 'hello') {
        if (handshakeComplete) {
          sendMessage(transport, { type: 'error', message: 'duplicate hello' });
          return;
        }
        if (payload.version !== PROTOCOL_VERSION) {
          sendMessage(transport, { type: 'error', message: 'protocol version mismatch' });
          await cleanup(true);
          return;
        }
        handshakeComplete = true;
        sendMessage(transport, { type: 'hello', role: 'worker', version: PROTOCOL_VERSION });
        return;
      }

      if (!handshakeComplete) {
        sendMessage(transport, { type: 'error', message: 'handshake required' });
        return;
      }

      switch (payload.type) {
        case 'run': {
          if (runtime.isRunning()) {
            sendMessage(transport, { type: 'error', message: 'run already in progress' });
            return;
          }
          try {
            runtime.startRun(payload.config);
            sendMessage(transport, { type: 'run-accepted' });
          } catch (err) {
            const message = err instanceof Error ? err.message : 'failed to start run';
            sendMessage(transport, { type: 'error', message });
          }
          break;
        }
        case 'event': {
          if (!runtime.isRunning()) {
            sendMessage(transport, { type: 'error', message: 'no active run' });
            return;
          }
          try {
            const item = wireToStreamItem(payload.item);
            runtime.enqueue(item);
          } catch (err) {
            sendMessage(transport, { type: 'error', message: 'failed to ingest event' });
          }
          break;
        }
        case 'event-batch': {
          if (!runtime.isRunning()) {
            sendMessage(transport, { type: 'error', message: 'no active run' });
            return;
          }
          if (!Array.isArray(payload.items) || payload.items.length === 0) {
            sendMessage(transport, { type: 'error', message: 'empty event batch' });
            return;
          }
          try {
            const items = payload.items.map(wireToStreamItem);
            runtime.enqueueBatch(items);
          } catch (err) {
            sendMessage(transport, { type: 'error', message: 'failed to ingest batch' });
          }
          break;
        }
        case 'end': {
          console.log('[worker] received end of stream');
          if (!runtime.isRunning()) {
            sendMessage(transport, { type: 'error', message: 'no active run' });
            return;
          }
          try {
            const summary = await runtime.finishRun();
            sendMessage(transport, { type: 'summary', summary });
          } catch (err) {
            sendMessage(transport, { type: 'error', message: err instanceof Error ? err.message : 'run failed' });
          }
          break;
        }
        default:
          sendMessage(transport, { type: 'error', message: 'unknown message type' });
      }
    });
  transport.onClose(async () => {
    await cleanup();
  });

  transport.onError(async () => {
    await cleanup();
  });
};

const startServer = () => {
  const server = net.createServer(socket => {
    const transport = createSocketTransport(socket);
    handleTransport(transport);
  });

  server.listen(DEFAULT_PORT, DEFAULT_HOST, () => {
    console.log(`[worker] listening on ${DEFAULT_HOST}:${DEFAULT_PORT}`);
  });
};

startServer();

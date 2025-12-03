import { ClientMessage, ServerMessage, wireToStreamItem } from './socketProtocol';
import { WorkerRuntime } from './workerRuntime';
import { LmdbDurability } from './docStore';

export type LineHandler<Line = string> = (line: Line) => void;
export type VoidHandler = () => void;
export type ErrorHandler = (error: Error) => void;

const PROTOCOL_VERSION = 1;
const DOCSTORE_DURABILITY: LmdbDurability = process.env.THUNDERDB_DOCSTORE_DURABILITY === 'relaxed' ? 'relaxed' : 'durable';
const WORKER_PROGRESS_STEP = Math.max(1, Number(process.env.WORKER_PROGRESS_STEP ?? 10000));
const debugEvictions = process.env.PERF_DEBUG_EVICS === '1';

export interface LineTransport<Line = string, CoLine = string> {
  send(line: Line): void;
  onLine(handler: LineHandler<CoLine>): void;
  onClose(handler: VoidHandler): void;
  onError(handler: ErrorHandler): void;
  close(): void;
}

class InProcessBridge<ClientLine, ServerLine> {
  private serverLineHandlers: LineHandler<ServerLine>[] = [];
  private clientLineHandlers: LineHandler<ClientLine>[] = [];
  private serverCloseHandlers: VoidHandler[] = [];
  private clientCloseHandlers: VoidHandler[] = [];
  private serverErrorHandlers: ErrorHandler[] = [];
  private clientErrorHandlers: ErrorHandler[] = [];
  private closed = false;

  addServerLine(handler: LineHandler<ServerLine>): void {
    this.serverLineHandlers.push(handler);
  }

  addClientLine(handler: LineHandler<ClientLine>): void {
    this.clientLineHandlers.push(handler);
  }

  addServerClose(handler: VoidHandler): void {
    this.serverCloseHandlers.push(handler);
  }

  addClientClose(handler: VoidHandler): void {
    this.clientCloseHandlers.push(handler);
  }

  addServerError(handler: ErrorHandler): void {
    this.serverErrorHandlers.push(handler);
  }

  addClientError(handler: ErrorHandler): void {
    this.clientErrorHandlers.push(handler);
  }

  sendToServer(line: ServerLine): void {
    if (this.closed) throw new Error('in-process transport closed');
    for (const handler of this.serverLineHandlers) handler(line);
  }

  sendToClient(line: ClientLine): void {
    if (this.closed) return;
    for (const handler of this.clientLineHandlers) handler(line);
  }

  close(from: 'server' | 'client'): void {
    if (this.closed) return;
    this.closed = true;
    const first = from === 'server' ? this.serverCloseHandlers : this.clientCloseHandlers;
    const second = from === 'server' ? this.clientCloseHandlers : this.serverCloseHandlers;
    for (const handler of first) setImmediate(handler);
    for (const handler of second) setImmediate(handler);
  }

  error(err: Error): void {
    for (const handler of this.serverErrorHandlers) setImmediate(() => handler(err));
    for (const handler of this.clientErrorHandlers) setImmediate(() => handler(err));
  }
}

class InProcessServerTransport<ClientLine, ServerLine> implements LineTransport<ClientLine, ServerLine> {
  constructor(private readonly bridge: InProcessBridge<ClientLine, ServerLine>) { }

  send(line: ClientLine): void {
    this.bridge.sendToClient(line);
  }

  onLine(handler: LineHandler<ServerLine>): void {
    this.bridge.addServerLine(handler);
  }

  onClose(handler: VoidHandler): void {
    this.bridge.addServerClose(handler);
  }

  onError(handler: ErrorHandler): void {
    this.bridge.addServerError(handler);
  }

  close(): void {
    this.bridge.close('server');
  }
}

export interface InProcessWorkerClient<Line, CoLine> {
  send(line: Line): void;
  onLine(handler: LineHandler<CoLine>): void;
  onClose(handler: VoidHandler): void;
  onError(handler: ErrorHandler): void;
  close(): void;
}

class InProcessClientTransport<ClientLine, ServerLine> implements InProcessWorkerClient<ServerLine, ClientLine> {
  constructor(private readonly bridge: InProcessBridge<ClientLine, ServerLine>) { }

  send(line: ServerLine): void {
    this.bridge.sendToServer(line);
  }

  onLine(handler: LineHandler<ClientLine>): void {
    this.bridge.addClientLine(handler);
  }

  onClose(handler: VoidHandler): void {
    this.bridge.addClientClose(handler);
  }

  onError(handler: ErrorHandler): void {
    this.bridge.addClientError(handler);
  }

  close(): void {
    this.bridge.close('client');
  }
}

const log: typeof console.log = debugEvictions ? () => { } : console.log

export const handleTransport = <ClientLine, ServerLine>(transport: LineTransport<ClientLine, ServerLine>, sendMessage: (transport: LineTransport<ClientLine, ServerLine>, message: ServerMessage) => void, parse: (line: ServerLine) => ClientMessage) => {
  let handshakeComplete = false;
  let closing = false;
  const runtime = new WorkerRuntime({
    docStoreDurability: DOCSTORE_DURABILITY,
    progressStep: WORKER_PROGRESS_STEP,
    log: message => log(message),
  });

  const cleanup = (closeTransport = false) => {
    if (closing) return;
    closing = true;
    if (closeTransport) transport.close();
  };

  transport.onLine(line => {
    let payload: ClientMessage;
    try {
      payload = parse(line);
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
        cleanup(true);
        return;
      }
      handshakeComplete = true;
      runtime.hello();
      sendMessage(transport, { type: 'hello', role: 'worker', version: PROTOCOL_VERSION });
      return;
    }

    if (!handshakeComplete) {
      sendMessage(transport, { type: 'error', message: 'handshake required' });
      return;
    }

    switch (payload.type) {
      case 'event': {
        try {
          const item = wireToStreamItem(payload.item);
          runtime.enqueueBatch(item);
        } catch (err) {
          console.error(err)
          sendMessage(transport, { type: 'error', message: 'failed to ingest event' });
        }
        break;
      }
      case 'end': {
        log('[worker] received end of stream');
        try {
          log('[worker] finishing run...');
          const summary = runtime.finishRun();
          log('[worker] run finished');
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
  transport.onClose(() => {
    cleanup();
  });

  transport.onError(() => {
    cleanup();
  });
};


export const createInProcessWorkerClient = (): InProcessWorkerClient<ClientMessage, ServerMessage> => {

  log('[worker] starting in-process worker client');
  const bridge = new InProcessBridge<ServerMessage, ClientMessage>();
  const serverTransport = new InProcessServerTransport(bridge);
  const clientTransport = new InProcessClientTransport(bridge);
  handleTransport(serverTransport, (transport, message) => transport.send(message), line => line);
  return clientTransport;
};
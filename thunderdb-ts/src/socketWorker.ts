import dotenv from 'dotenv';
import net from 'node:net';
import readline from 'node:readline';
import { ErrorHandler, handleTransport, LineHandler, LineTransport, VoidHandler } from './transport';
import { ServerMessage } from './socketProtocol';

dotenv.config();

const DEFAULT_PORT = Number(process.env.WORKER_PORT ?? 4040);
const DEFAULT_HOST = process.env.WORKER_HOST ?? '0.0.0.0';


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

const startServer = () => {
  const server = net.createServer(socket => {
    const transport = createSocketTransport(socket);
    handleTransport(transport, sendMessage, JSON.parse);
  });

  server.listen(DEFAULT_PORT, DEFAULT_HOST, () => {
    console.log(`[worker] listening on ${DEFAULT_HOST}:${DEFAULT_PORT}`);
  });
};

startServer();

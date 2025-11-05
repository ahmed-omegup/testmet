import r from 'rethinkdb';
import { WebSocketServer } from 'ws';
import express from 'express';
import http from 'http';

const RETHINKDB_HOST = process.env.RETHINKDB_HOST || 'rethinkdb';
const RETHINKDB_PORT = parseInt(process.env.RETHINKDB_PORT || '28015');
const PORT = parseInt(process.env.PORT || '3000');

let conn = null;
const clients = new Map(); // Map<ws, {subscriptions: Map<subId, cursor>}>

// Connect to RethinkDB
async function connectDB() {
  try {
    conn = await r.connect({ host: RETHINKDB_HOST, port: RETHINKDB_PORT });
    console.log('Connected to RethinkDB');
    
    // Ensure database and table exist
    await setupDatabase();
    
    return conn;
  } catch (err) {
    console.error('Failed to connect to RethinkDB:', err);
    setTimeout(connectDB, 5000);
  }
}

async function setupDatabase() {
  try {
    // Create database if not exists
    const dbList = await r.dbList().run(conn);
    if (!dbList.includes('benchmark')) {
      await r.dbCreate('benchmark').run(conn);
      console.log('Created database: benchmark');
    }
    
    // Create table if not exists
    const tableList = await r.db('benchmark').tableList().run(conn);
    if (!tableList.includes('docs')) {
      await r.db('benchmark').tableCreate('docs').run(conn);
      console.log('Created table: docs');
      
      // Create index on score for efficient queries
      await r.db('benchmark').table('docs').indexCreate('score').run(conn);
      await r.db('benchmark').table('docs').indexWait('score').run(conn);
      console.log('Created index on score');
    }
  } catch (err) {
    console.error('Setup database error:', err);
    throw err;
  }
}

// Express app for health check
const app = express();
app.get('/health', (req, res) => {
  res.status(conn ? 200 : 503).send(conn ? 'OK' : 'Not ready');
});

const server = http.createServer(app);

// WebSocket server
const wss = new WebSocketServer({ server, path: '/websocket' });

wss.on('connection', (ws) => {
  console.log('Client connected');
  
  // Initialize client state
  clients.set(ws, { subscriptions: new Map() });
  
  ws.on('message', async (data) => {
    try {
      const msg = JSON.parse(data.toString());
      
      switch (msg.msg) {
        case 'connect':
          // Send connected response
          ws.send(JSON.stringify({ msg: 'connected', session: Math.random().toString(36) }));
          break;
          
        case 'sub':
          await handleSubscription(ws, msg);
          break;
          
        case 'unsub':
          await handleUnsubscribe(ws, msg);
          break;
          
        default:
          console.log('Unknown message type:', msg.msg);
      }
    } catch (err) {
      console.error('Message handling error:', err);
      ws.send(JSON.stringify({ msg: 'error', reason: err.message }));
    }
  });
  
  ws.on('close', () => {
    console.log('Client disconnected');
    cleanup(ws);
  });
  
  ws.on('error', (err) => {
    console.error('WebSocket error:', err);
    cleanup(ws);
  });
});

async function handleSubscription(ws, msg) {
  const { id, name, params } = msg;
  
  if (name !== 'latestDocs') {
    ws.send(JSON.stringify({ msg: 'nosub', id, error: { error: 404, reason: 'Subscription not found' } }));
    return;
  }
  
  const [minScore, maxScore] = params;
  
  if (typeof minScore !== 'number' || typeof maxScore !== 'number') {
    ws.send(JSON.stringify({ msg: 'nosub', id, error: { error: 400, reason: 'Invalid parameters' } }));
    return;
  }
  
  try {
    // Initial query - get current matching documents
    const initialDocs = await r.db('benchmark')
      .table('docs')
      .between(minScore, maxScore, { index: 'score' })
      .orderBy(r.desc('timestamp'))
      .limit(50)
      .run(conn);
    
    const docsArray = await initialDocs.toArray();
    
    // Send initial data
    for (const doc of docsArray) {
      ws.send(JSON.stringify({
        msg: 'added',
        collection: 'docs',
        id: doc.id,
        fields: {
          name: doc.name,
          score: doc.score,
          timestamp: doc.timestamp
        }
      }));
    }
    
    // Send ready
    ws.send(JSON.stringify({ msg: 'ready', subs: [id] }));
    
    // Setup changefeed for real-time updates
    const changeCursor = await r.db('benchmark')
      .table('docs')
      .between(minScore, maxScore, { index: 'score' })
      .changes({ includeInitial: false })
      .run(conn);
    
    // Store cursor for cleanup
    const client = clients.get(ws);
    if (client) {
      client.subscriptions.set(id, changeCursor);
    }
    
    // Handle changefeed events
    changeCursor.each((err, change) => {
      if (err) {
        console.error('Changefeed error:', err);
        return;
      }
      
      if (!change) return;
      
      try {
        if (change.old_val && change.new_val) {
          // Update
          ws.send(JSON.stringify({
            msg: 'changed',
            collection: 'docs',
            id: change.new_val.id,
            fields: {
              name: change.new_val.name,
              score: change.new_val.score,
              timestamp: change.new_val.timestamp
            }
          }));
        } else if (change.new_val) {
          // Insert
          ws.send(JSON.stringify({
            msg: 'added',
            collection: 'docs',
            id: change.new_val.id,
            fields: {
              name: change.new_val.name,
              score: change.new_val.score,
              timestamp: change.new_val.timestamp
            }
          }));
        } else if (change.old_val) {
          // Delete
          ws.send(JSON.stringify({
            msg: 'removed',
            collection: 'docs',
            id: change.old_val.id
          }));
        }
      } catch (sendErr) {
        console.error('Failed to send change:', sendErr);
      }
    });
    
  } catch (err) {
    console.error('Subscription error:', err);
    ws.send(JSON.stringify({ msg: 'nosub', id, error: { error: 500, reason: err.message } }));
  }
}

async function handleUnsubscribe(ws, msg) {
  const { id } = msg;
  const client = clients.get(ws);
  
  if (client && client.subscriptions.has(id)) {
    const cursor = client.subscriptions.get(id);
    try {
      await cursor.close();
    } catch (err) {
      console.error('Error closing cursor:', err);
    }
    client.subscriptions.delete(id);
  }
  
  ws.send(JSON.stringify({ msg: 'nosub', id }));
}

function cleanup(ws) {
  const client = clients.get(ws);
  if (client) {
    // Close all subscriptions
    for (const [id, cursor] of client.subscriptions) {
      cursor.close().catch(err => console.error('Error closing cursor:', err));
    }
    clients.delete(ws);
  }
}

// Start server
connectDB().then(() => {
  server.listen(PORT, () => {
    console.log(`RethinkDB server listening on port ${PORT}`);
  });
});

// Graceful shutdown
process.on('SIGTERM', async () => {
  console.log('SIGTERM received, closing connections...');
  
  // Close all client connections
  for (const [ws, client] of clients) {
    for (const cursor of client.subscriptions.values()) {
      await cursor.close();
    }
    ws.close();
  }
  
  if (conn) {
    await conn.close();
  }
  
  process.exit(0);
});

// Common utilities and configuration
export const MONGO_URL = process.env.MONGO_URL;
export const METEOR_URL = process.env.METEOR_URL || process.env.SERVER_URL;
export const RETHINKDB_HOST = process.env.RETHINKDB_HOST;
export const RETHINKDB_PORT = parseInt(process.env.RETHINKDB_PORT || '28015');

export const CUSTOMERS = parseInt(process.env.CUSTOMERS || "20000");
export const DURATION = parseInt(process.env.DURATION || "10");
export const INIT_TIME = parseInt(process.env.INIT_TIME || "10");
export const N = parseInt(process.env.DOCUMENTS || "1000000");
export const DENSITY = parseFloat(process.env.DENSITY || "10"); // N/RANGE
export const RANGE = N / DENSITY;

// Deterministic PRNG
function prng(seed) {
  return () => (seed = (seed * 48271) % 0x7fffffff) / 0x7fffffff;
}
export const rand = prng(42);

export const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// Fatal error handler - stop entire cluster on first error
export function fatal(msg, err) {
  console.error(`FATAL ERROR: ${msg}`);
  if (err) console.error(err);
  process.exit(1);
}

// Customer range calculation
export function customerRange(c) {
  const width = 100 + rand() * 500;
  const a = rand() * (RANGE - width);
  return [Math.floor(a), Math.floor(a + width)];
}

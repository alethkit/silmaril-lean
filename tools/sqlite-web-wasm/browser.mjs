import { readFile } from 'node:fs/promises';
import { createServer } from 'node:http';
import { join } from 'node:path';
import { createRequire } from 'node:module';

const require = createRequire(import.meta.url);
const { chromium } = require('playwright');
const [directory, wasm, executablePath] = process.argv.slice(2);
if (process.argv.length !== 5) {
  throw new Error('expected the release directory, Wasm path and Chromium executable');
}
const prefix = '/jswasm/';
const paths = new Map([
  [prefix + 'sqlite3.mjs', ['text/javascript', await readFile(join(directory, 'jswasm/sqlite3.mjs'))]],
  [prefix + 'sqlite3.wasm', ['application/wasm', await readFile(wasm)]]
]);
const server = createServer((request, response) => {
  response.setHeader('Cross-Origin-Opener-Policy', 'same-origin');
  response.setHeader('Cross-Origin-Embedder-Policy', 'require-corp');
  if (request.url === '/') {
    response.setHeader('Content-Type', 'text/html');
    response.end('<!doctype html><title>SQLite web smoke check</title>');
  } else if (paths.has(request.url)) {
    const [type, bytes] = paths.get(request.url);
    response.setHeader('Content-Type', type);
    response.end(bytes);
  } else {
    response.writeHead(404).end();
  }
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
try {
  const browser = await chromium.launch({ executablePath, args: ['--no-sandbox'] });
  try {
    const page = await browser.newPage();
    await page.goto(`http://127.0.0.1:${server.address().port}`);
    const result = await page.evaluate(async () => {
      const { default: initialize } = await import('/jswasm/sqlite3.mjs');
      const sqlite = await initialize();
      const db = new sqlite.oo1.DB(':memory:', 'c');
      try {
        db.exec('CREATE TABLE t(n); INSERT INTO t VALUES (7),(14),(21);');
        const bytes = await (await fetch('/jswasm/sqlite3.wasm')).arrayBuffer();
        const artifact = await WebAssembly.compile(bytes);
        return {
          libversion: sqlite.capi.sqlite3_libversion(),
          version: sqlite.capi.sqlite3_libversion_number(),
          sourceId: sqlite.capi.sqlite3_sourceid(),
          sql: db.selectValue('SELECT sum(n) FROM t'),
          imports: WebAssembly.Module.imports(artifact),
          exports: WebAssembly.Module.exports(artifact)
        };
      } finally { db.close(); }
    });
    const expectedSourceId =
      '2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76';
    if (result.libversion !== '3.54.1' || result.version !== 3054001 ||
        result.sourceId !== expectedSourceId || result.sql !== 42) {
      throw new Error(JSON.stringify(result));
    }
    console.log(JSON.stringify({ browser: browser.version(), ...result }, null, 2));
  } finally { await browser.close(); }
} finally { server.close(); }

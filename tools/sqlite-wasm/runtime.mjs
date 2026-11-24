import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { WASI } from 'node:wasi';

const [leanVersion, ...paths] = process.argv.slice(2);
assert.ok(/^\d+$/.test(leanVersion) && paths.length > 0, 'expected Lean result and Wasm paths');

for (const path of paths) {
  const wasi = new WASI({ version: 'preview1', args: [], env: {}, preopens: {} });
  const { instance } = await WebAssembly.instantiate(readFileSync(path), wasi.getImportObject());
  wasi.initialize(instance);
  const e = instance.exports;
  const version = e.sqlite3_libversion_number();
  assert.equal(version, Number(leanVersion), 'sqlite3_libversion_number versus Lean');

  function cString(value) {
    const bytes = Buffer.from(value + '\0');
    const ptr = e.malloc(bytes.length);
    assert.ok(ptr > 0);
    new Uint8Array(e.memory.buffer).set(bytes, ptr);
    return ptr;
  }

  const output = e.malloc(4);
  assert.ok(output > 0);
  const pointerAtOutput = () => new DataView(e.memory.buffer).getUint32(output, true);
  const filename = cString(':memory:');
  assert.equal(e.sqlite3_open(filename, output), 0);
  const db = pointerAtOutput();

  const sql = cString('WITH t(n) AS (VALUES (7), (14), (21)) SELECT sum(n) FROM t');
  assert.equal(e.sqlite3_prepare_v2(db, sql, -1, output, 0), 0);
  const stmt = pointerAtOutput();
  assert.equal(e.sqlite3_step(stmt), 100); // SQLITE_ROW
  assert.equal(e.sqlite3_column_int(stmt, 0), 42);
  assert.equal(e.sqlite3_step(stmt), 101); // SQLITE_DONE
  assert.equal(e.sqlite3_finalize(stmt), 0);
  assert.equal(e.sqlite3_close(db), 0);
  for (const ptr of [sql, filename, output]) e.free(ptr);

  console.log(`${path}: sqlite3_libversion_number=${version}, query result=42`);
}

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { WASI } from 'node:wasi';

const [wasm, vectors] = process.argv.slice(2);
assert.ok(wasm && vectors, 'expected the exported test copy and Lean vectors');
const cases = JSON.parse(readFileSync(vectors, 'utf8'));
const wasi = new WASI({ version: 'preview1', args: [], env: {}, preopens: {} });
const module = new WebAssembly.Module(readFileSync(wasm));
const imports = WebAssembly.Module.imports(module);
assert.equal(imports.length, 23);
assert.ok(imports.every(i => i.kind === 'function' && i.module === 'wasi_snapshot_preview1'));
const instance = new WebAssembly.Instance(module, wasi.getImportObject());
wasi.initialize(instance);
const e = instance.exports;
const ptr = e.malloc(32);
assert.ok(ptr > 0 && ptr % 8 === 0);
const region = new Uint8Array(e.memory.buffer, ptr, 32);
const out = new DataView(e.memory.buffer, ptr + 16, 8);
const sentinel = 0xa5;

for (const { value, bytes } of cases.encode) {
  region.fill(sentinel);
  const width = e.sqlite3PutVarint(ptr, BigInt(value));
  assert.equal(width, bytes.length, `encoded width for ${value}`);
  const expected = new Uint8Array(32).fill(sentinel);
  expected.set(bytes);
  assert.deepEqual(region, expected, `encoded bytes and write bounds for ${value}`);
}

for (const { bytes, value, width } of cases.decode) {
  region.fill(sentinel);
  region.set(bytes);
  const expected = region.slice();
  new DataView(expected.buffer).setBigUint64(16, BigInt(value), true);
  assert.equal(e.sqlite3GetVarint(ptr, ptr + 16), width, `decoded width for ${bytes}`);
  assert.equal(out.getBigUint64(0, true), BigInt(value), `decoded value for ${bytes}`);
  assert.deepEqual(region, expected, `input bytes and write bounds for ${bytes}`);
}

e.free(ptr);
const allWidths = [1, 2, 3, 4, 5, 6, 7, 8, 9];
assert.deepEqual([...new Set(cases.encode.map(row => row.bytes.length))].sort(), allWidths);
assert.deepEqual([...new Set(cases.decode.map(row => row.width))].sort(), allWidths);
console.log(`PASS ${cases.encode.length} encodes and ${cases.decode.length} complete decodes across widths 1–9`);

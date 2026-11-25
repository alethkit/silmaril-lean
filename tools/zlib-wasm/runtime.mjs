import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';

const bytes = await readFile(process.argv[2]);
const { instance } = await WebAssembly.instantiate(bytes);
const ptr = 1024;
const memory = new Uint8Array(instance.exports.memory.buffer);
const vectors = [
  [new TextEncoder().encode('Wikipedia'), 0x11e60398],
  [Uint8Array.of(255), 0x01000100],
  [Uint8Array.from({ length: 5553 }, (_, i) => (17 * i + 3) % 256), 0x128fcd82],
];
for (const checksum of [instance.exports.adler32, instance.exports.adler32_z]) {
  assert.equal(checksum(0, 0, 0) >>> 0, 1, 'initial state');
  for (const [input, expected] of vectors) {
    memory.set(input, ptr);
    assert.equal(checksum(1, ptr, input.length) >>> 0, expected);
  }
}
console.log(`Node ${process.version}: both exports passed initialization and three byte vectors`);

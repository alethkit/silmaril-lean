import { readFile } from "node:fs/promises";
import { strictEqual } from "node:assert/strict";

const binary = await readFile(process.argv[2]);
const { instance } = await WebAssembly.instantiate(binary);
const roundA = instance.exports.sha256_round_a;

// NIST SHA256.pdf, pp. 1–2, “abc” working variables at t=0 and t=1.
const cases = [
  [
    [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
      0x5be0cd19, 0x428a2f98, 0x61626380],
    0x5d6aebcd,
  ],
  [
    [0x5d6aebcd, 0x6a09e667, 0xbb67ae85, 0xfa2a4622, 0x510e527f, 0x9b05688c,
      0x1f83d9ab, 0x71374491, 0],
    0x5a6ad9ad,
  ],
];

for (const [index, [inputs, expected]] of cases.entries()) {
  strictEqual(roundA(...inputs) >>> 0, expected, `NIST abc round ${index}`);
}
console.log(`Native WebAssembly matched ${cases.length} published NIST round values`);

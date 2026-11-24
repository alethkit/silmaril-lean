# SQLite reactor three-byte helper proof

[`ThreeByteHelper.lean`](ThreeByteHelper.lean) proves `quotedHelper_threeByte`
for the actual function selected at index 547 of `SqliteWasm.sqlite`.
The theorem applies to every unsigned input in `[16384, 2097152)` and every
store satisfying [the disjoint-buffer contract](three-byte.md). It proves
Core reachability from the entered helper to exactly i32 3, with the caller
frame restored and only the specified output and scratch slices written.
The global holding the stack pointer is preserved.

The same file proves `putVarint_threeByte` for calls through the quoted
function at index 530 with the specified runtime function bindings and
callee memory and global lookups. The output is `Varint.encode` and scratch
at stack pointer minus 10 holds those three bytes in reverse order.
[Original-byte linkage for these functions](ArtifactCheck.lean)

The verification conditions come from the actual quoted instruction tree.
The digit-loop invariant tracks the current i64 as the original value
shifted by seven bits per iteration, the i32 digit count and the exact
scratch prefix. The unsigned comparison returns to the loop for the first
two iterations, then the helper loads and clears the continuation bit at
the first scratch byte. The copy-loop invariant tracks the count,
descending scratch address and exact output prefix. The range separation
lets each packed load see the scratch digit after earlier output writes.
The loop compares the new count with 3 and exits after the third copy.
Both invariants use a decreasing variant. The width-nine branch is
unreachable under the three-byte precondition.
[Memory and digit lemmas](ThreeByteLoopMemory.lean)

The kernel checks the generated conditions, the total-correctness argument
and its conversion to Core reachability. The exact store postcondition
covers the admitted disjoint buffers. Overlapping buffers, other widths and
whole-module behavior are outside its scope.

Run the pinned fixture and both symbolic proof modules using the
[documented reactor inputs](README.md#reproduce).

```sh
bash tools/sqlite-wasm/check-three-byte-loops.sh "$inputs" .lake/sqlite-wasm-three-byte-loops
```

Add `.lake/sqlite-wasm-three-byte-loops/lean` to `LEAN_PATH` and import
`SqliteWasm.ThreeByteHelper` in an ordinary Lean module. The checker prints
the axiom audit for the two behavior theorems.

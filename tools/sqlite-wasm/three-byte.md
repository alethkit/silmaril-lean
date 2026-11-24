# Three-byte SQLite reactor varint contract

[`ThreeByteContract.lean`](ThreeByteContract.lean) proves that the quoted
reactor's function 530 skips both inline cases for an unsigned input of at
least 16,384, forwards the original i32/i64 arguments to slot 547, and
restores the caller frame after the helper returns. The call theorem takes
the two runtime function bindings and an exact Core execution of the
quoted helper as premises. The original-artifact theorem identifies the
two quoted bodies from the pinned original bytes.
[Artifact checks](ArtifactCheck.lean)

The `HelperContract` proposition describes the remaining width-three proof
over `16384 ≤ x < 2097152`. In the helper's instance, memory 0 supplies
the byte image and global 0 supplies the i32 stack pointer. The output and
scratch intervals each occupy three bytes, lie in bounds, and are disjoint.
Scratch starts at `stackPointer - 10`, with `stackPointer ≥ 16` so that
the helper's address calculation does not wrap. The post-store replaces
the scratch range with the reverse of `Varint.encode x`, then writes
`Varint.encode x` to the output. The result is exactly i32 3. The file
proves the scratch-address identity and the three-byte digit formulas for
the entire interval.

[`ThreeByteWitness.lean`](ThreeByteWitness.lean) checks the entered helper
with the one-page typed fixture, output at 16 and stack pointer 128. It
transfers the kernel evaluations to Core reachability and composes both
with the wrapper theorem.

| Input | Scratch at 118–120 | Output at 16–18 |
| ---: | --- | --- |
| 16,384 | `00 80 81` | `81 80 00` |
| 2,097,151 | `7f ff ff` | `ff ff 7f` |

The universal `HelperContract` is a proposition with two remaining
symbolic execution obligations. After digit-loop iteration `j`, local 1
must hold `x >>> (7*j)`, local 3 must hold `j`, and just the first
`j` scratch bytes must contain the low digits with their continuation
bits set. A separate load/mask/store clears the first continuation bit.
After copy-loop iteration `j`, local 2 must hold `j`, local 4 must
track the descending scratch address, and exactly the first `j` output
bytes must equal the matching reversed scratch bytes. The proof needs
packed loads after scratch stores and after disjoint output writes,
then equality of the individual stores and the two final splices.
Widths beyond three and overlapping buffers are outside this contract.

Run the pinned reactor check and compile both theorem modules with its
[documented inputs](README.md#reproduce).

```sh
bash tools/sqlite-wasm/check-three-byte.sh "$inputs" .lake/sqlite-wasm-three-byte
```

The generated Lean root is `.lake/sqlite-wasm-three-byte/lean`. Add it to
`LEAN_PATH` to import `SqliteWasm.ThreeByteContract` or
`SqliteWasm.ThreeByteWitness` in an ordinary Lean module. The checker prints
the axiom audit for the new proofs.

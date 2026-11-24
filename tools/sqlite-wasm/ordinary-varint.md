# Ordinary SQLite reactor varint widths

[`OrdinaryVarintHelper.lean`](OrdinaryVarintHelper.lean) proves
`putVarint_ordinary` for the quoted reactor wrapper at slot 530 and its
helper at slot 547. The width is a parameter from three through eight,
with input bounds `128^(width - 1) ≤ value < 128^width`.
`existsWidth` shows that these cases cover every input in
`[16384, 2^56)`. The proof uses the stated function bindings and
types, a stack pointer in callee global 0, and disjoint, nonwrapping,
in-bounds spans in callee memory 0.

The call returns the width as i32, restores the caller frame, writes
`Varint.encode` to the output, and leaves its reverse in scratch at
stack pointer minus 10. The exact store expression preserves every other
byte and the stack-pointer global. The entered helper theorem also
covers positive values of width one or two under its own memory premises.
The wrapper handles those widths inline. Width nine and overlapping
spans are outside this proof.
[Selected original Code records](ArtifactCheck.lean)

One closed verification-condition list is generated from the actual
quoted helper. The digit loop tracks the remaining i64 and exact
scratch prefix. The shifted i64 and original value are each split
into two i32 terms for the memory predicates. The proof checks their
exact reconstruction, uses the base-128 interval to determine when
the loop exits, and accounts for the continuation-bit clear. The
reverse-copy invariant uses the descending scratch address and exact
output prefix. Disjointness preserves later scratch reads and the
variant reaches zero when the copy count reaches the width.
[Encoding and memory lemmas](OrdinaryVarintMemory.lean)

The existing [three-byte checker](three-byte-loops.md) still checks its
original behavior theorems and downstream consumer. The new consumer applies
the parameterized theorem through ordinary imports at the width-four
transition, at `2^32`, and at the largest ordinary value.
[Import checks](OrdinaryVarintImport.lean)

Use the [pinned reactor inputs](README.md#reproduce).

```sh
bash tools/sqlite-wasm/check-ordinary-varint.sh "$inputs" .lake/sqlite-wasm-ordinary-varint
```

Add `.lake/sqlite-wasm-ordinary-varint/lean` to `LEAN_PATH` and import
`SqliteWasm.OrdinaryVarintHelper`. The checker prints the axiom audit.

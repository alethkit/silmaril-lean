# Overlapping zero read in the directly prepared SQLite reactor

`SqliteWasm.reactorPreparedZeroRead` gives a fixed call to the pinned
internal varint reader at slot 434. The canonical typed fixture's
directly prepared memory has a zero word at byte 59328 and size 131072.
The proof derives the first zero octet from the word, checks the
one-octet `Varint.read?` result, and establishes the eight-byte
destination bound.

With source and destination both 59328, the Core call reaches i32 1
in the original caller frame. The exact resulting store is the
initial store with eight zero bytes spliced at byte 59328 in the
mapped callee memory. The statement supplies the prepared state and
memory mapping for the canonical typed fixture.

An ordinary downstream Lean file composes the theorem with
`originalDecode` on the pinned original bytes. The same file also
kernel-replays the fixed-address slot-434 call with 64 steps of fuel
in a directly linked zero-memory model. That replay checks the
entire resulting configuration.

## Reproduce

Build the successful reader and ordinary decoder in a common generated
root using the [prepared-reader prerequisites](../prepared-varint-reader/README.md#reproduce).
Run the zero-read checker in that root.

```sh
bash tools/sqlite-wasm/prepared-varint-zero-read/check.sh WORK_DIR/lean/SqliteWasm
```

The checker builds the prepared-reader proof, this fixed witness and
its ordinary consumer. It prints the kernel axiom dependencies.

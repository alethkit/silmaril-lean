# Initialize the prepared SQLite reactor, then call its version export

`SqliteWasm.reactorPreparedInitVersion` uses the common
`prepareDirect?` result to resolve both named exports in the same
canonical typed fixture. The zero-argument `_initialize` call returns
no values in the empty invoke frame. Its final store is exactly
`runtime.setMem memoryAddress (threadSetupMemory (initializerMark mem 0) 0)`.

That memory update preserves the allocated entry for
`sqlite3_libversion_number`. The zero-argument version call starts in
the initializer's final store and returns i32 3054001 in the empty
invoke frame, preserving that entire store. The version linkage is
reused from `reactorPreparedVersionExportWithEntry`, which proves
invocation given the same allocated function entry. The existing
`reactorPreparedVersionExport` theorem specializes it to the
original prepared store.

The ordinary consumer derives the sequence from `originalDecode`.
The scoped theorem covers Core execution after direct preparation of
the pinned reactor.

The separate executable replay links the four quoted functions in a
small fixture with a nonzero source word. It checks both returns and
frames, the exact initializer memory, and memory preservation when the
version call consumes the first call's output store. The Core theorem
and original-byte import are checked independently of this replay.

## Reproduce

Build the pinned source reactor and artifact checks.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder recipe](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then build both prepared export proofs,
the sequence theorem, and its ordinary consumer.

```sh
bash tools/sqlite-wasm/prepared-init-version/check.sh WORK_DIR/lean/SqliteWasm
```

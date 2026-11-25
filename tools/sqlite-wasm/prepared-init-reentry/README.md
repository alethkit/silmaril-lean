# Invoke the prepared SQLite reactor initializer twice

`SqliteWasm.reactorPreparedInitReentry` resolves the named
`_initialize` export in the canonical directly prepared reactor.
The first zero-argument invocation returns no values in the empty
invoke frame. Its exact output store installs
`threadSetupMemory (initializerMark mem 0) 0` at the allocated memory
address.

The second zero-argument invocation resolves the same allocated
function entry, memory, and base global in that store. The marker
word is 1 at address 59328. The existing nonzero-marker branch
reduces the second invocation to a Core trap in the empty invoke
frame. Its final configuration contains the entire first
invocation's output store.

The ordinary import applies the result to the pinned artifact via
`originalDecode`. The theorem concerns the canonical direct
preparation fixture and the Core invocation relation.

## Reproduce

Build the pinned source reactor and artifact checks.

```sh
bash tools/sqlite-wasm/check.sh ARCHIVE_DIR WORK_DIR
```

Follow the [whole-module decoder recipe](../whole-module/README.md#reproduce)
with `wasm` set to `WORK_DIR/sqlite3.wasm` and `quoted` to
`WORK_DIR/lean/SqliteWasm`. Then run the standalone checker.

```sh
bash tools/sqlite-wasm/prepared-init-reentry/check.sh WORK_DIR/lean/SqliteWasm
```

# Quoted reactor one-byte varint reader

`SqliteWasm.getVarint_oneByte` applies to the generated reactor object at
function index 434. Given a successful byte lookup at the i32 source address
with value below 128, it proves that `Varint.read?` on the initial linear
memory returns that value as a UInt64 and advances the Lean offset by one.
At the i32 destination address it requires eight bytes in bounds. The Core
call reaches i32 1 in the original caller frame, with the destination's eight
bytes replaced by the little-endian UInt64 and the rest of the store preserved.

The caller's function slot must resolve to a store entry with the selected
quoted code and runtime type `(i32, i32) -> i32`. Both accesses resolve memory
index 0 through the callee's module instance. The input and output may overlap
because the load completes before the store. The theorem uses the Core
small-step relation with an arbitrary numeric profile and host semantics.

The proof checks the executed instruction lists and nested block structure
against the quoted AST. Existing `originalGetVarintFunction` checks that the
function record independently selected from the original reactor bytes equals
the quoted record. That comparison covers the function's type index, locals,
and instruction tree. The signature theorem checks the quoted type separately.
The runtime linkage premises are explicit since neither check constructs a
runtime instance. The proof covers the branch for initial bytes 0 through 127.

From the repository root, with the pinned archives in `ARCHIVE_DIR`:

```sh
bash tools/sqlite-wasm/check-get-varint-one-byte.sh ARCHIVE_DIR WORK_DIR
```

This rebuilds the pinned reactor, generates the quote, checks the original
record, and compiles the proof with its axiom audit. An ordinary downstream
module imports the theorem and checks an overlapping call at byte 127 with
distinct caller and callee memory mappings, a nonempty caller frame, and
sentinels outside the exact eight-byte write.

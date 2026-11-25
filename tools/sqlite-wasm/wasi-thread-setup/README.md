# SQLite reactor WASI thread setup

`originalThreadSetupFunction` identifies defined function 1516 in the
decoded, pinned SQLite reactor. The pinned SDK linker map labels it
`__wasi_init_tp`. The kernel checks the exact body and locals against the
decomposition used by the proof. [Original decoder theorem](../whole-module/README.md) · [Artifact pin](../reactor.json)

`threadSetupReturns` gives a normal Core reduction of a call to slot 1516
when the caller slot and store entry resolve to this Wasm function with
runtime signature `() → ()`. The callee's memory 0 must resolve to an
instance with at least 59,984 bytes. The call returns no values and restores
the caller with only that memory instance updated by `threadSetupMemory`.
That definition lists the eight written i32 words in order. The word at
59,936 comes from an initial little-endian load at 59,892. All earlier
writes leave the load range untouched.

The actual branch uses the nonzero constant 126,112 and exits both blocks
after computing 65,536. The alternative code containing the global read
is skipped. The theorem works for any Core numeric profile and host
relation. Its reduction executes no global access or host call. Its scope
is a single linked call and its memory writes.

After the [original decoder check](../whole-module/README.md#reproduce), run

```sh
bash tools/sqlite-wasm/wasi-thread-setup/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

The downstream module imports `SqliteWasm.ThreadSetup` from the generated
Lean root and prints the three public theorems' axiom dependencies.
[Statements](ThreadSetup.lean) · [Downstream check](ImportCheck.lean)

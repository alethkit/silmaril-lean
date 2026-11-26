# A closed MLIR call to a WasmSSA leaf

`Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Thms` lowers the callee of a checked
MLIR `DirectCall` to a Core `FuncIdx`. The symbol's position in the ordered
signature table gives the index. Core's `Idx.ofNat?` rejects positions outside
`u32`. `callIndex?_lookup` recovers the symbol and exact profile at the emitted
index. `callIndex?_exists` guarantees an index when the signature table fits
in that index space. `emitCall?` also checks admission from a name and profile,
with `emitCall?_eq_some` characterizing successful emission. These laws apply
when Core functions are emitted in declaration order with no function imports.
[Emission and laws](../../Silmaril/Wasm/SSA/MLIR/WasmSSA/ModuleCall/Thms.lean) ·
[MLIR call admission](mlir-function-modules.md#function-signatures-and-direct-calls)

The fixture emits one Core module from a typed two-function source module.
Both functions have profile `(i64, i64) -> i64`. The exported `run` forwards
its parameters in order to the existing WasmSSA `selectDifference` leaf at
index 1 and returns its result. The module validator accepts the emitted shape.
The missing symbol, a wrong operand type, and a wrong result type each cause
call emission to fail. [Fixture definitions](../../Silmaril/Wasm/SSA/MLIR/WasmSSA/ModuleCall/Examples/Defs.lean) ·
[Checked observations](../../Silmaril/Wasm/SSA/MLIR/WasmSSA/ModuleCall/Examples/Thms.lean)

As in the closed allocation certificate in `CoreCert`, the initial store is
empty. `instantiate?` allocates the emitted module, and Lean proves this
configuration satisfies Core's `Instantiate` judgment. There are no imports,
segments, or start function. The wrapper and callee addresses come from the
allocated module instance, with checked export and store lookups. The proof
uses Core Logic's `wp_call` and the leaf's `Func.toWasm_returns` proof from
#3239. For every pair of `i64` words, the exported invocation has a Core run to
the source leaf's evaluated result in the same allocated store. Concrete runs
cover unequal inputs (`5, 9`, producing `0xfffffffffffffffc`) and equal inputs
(`5, 5`, producing `5`). [Closed allocation precedent](../../Silmaril/Wasm/SSA/CoreCert/Thms.lean) ·
[Core call rules](../../Silmaril/Wasm/Execution/Core/Step.lean) ·
[Core Logic rules](../../Silmaril/Wasm/Logic/Core/Thms.lean) ·
[WasmSSA leaf theorem](https://github.com/hiloopai/silmaril-lean/pull/3239)

The integration checks this one module and existential Core runs from its
instantiated store. General module linking, recursion, indirect calls and
every-run behavior are outside the claim. The Lean implementation is original
code using the repository's pinned WebAssembly 3.0 contract for direct calls,
allocation, instantiation, and invocation. [Core specification pin and file hashes](../../specs/wasm/core-3.0.json)

```sh
lake build --wfail +Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Examples.Thms
make check CHECK_TARGETS='+Silmaril.Wasm.SSA.MLIR.WasmSSA.ModuleCall.Examples.Thms +Silmaril.Wasm.SSA.MLIR.WasmSSA.Examples.Thms +Silmaril.SSA.MLIR.Module.Symbols.Examples.Thms'
```

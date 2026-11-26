# MLIR WasmSSA integer slice

The typed syntax models a single isolated `wasmssa.func` with integer parameters
and exactly one integer result. Upstream function parameters enter the body as
local references. In this slice they can only be read with `wasmssa.local_get`.
Each scalar binding introduces one fresh SSA value. Operand references carry
their type and can only name earlier bindings. Constants carry the decoded
32- or 64-bit pattern. `eqz` accepts either width and yields `i32`.
`lt_si` and `lt_ui` require operands of the same integer width and yield
`i32`. `select` requires an `i32` condition and two alternatives of the same
integer type.
The function model omits symbols, export and argument/result attributes, and
MLIR text and verifier interfaces.
[Integer syntax](../../Silmaril/SSA/MLIR/WasmSSA/Defs.lean)

## Upstream coverage

The 80 mnemonics below all have the prefix `wasmssa.`. The list is taken
from the pinned operation definitions and matches the generated operation
index. The 14 checked mnemonics cover the integer forms described above.
The other 66 mnemonics are planned.

| Status | Group | Mnemonics |
| --- | --- | --- |
| Checked | Function entry and exit | `func`, `local_get`, `return` |
| Checked | Scalar bindings | `const`, `add`, `sub`, `mul`, `and`, `or`, `xor`, `eqz`, `select` |
| Checked | Integer comparisons | `lt_si`, `lt_ui` |
| Planned | Structured control | `block`, `block_return`, `branch_if`, `if`, `loop` |
| Planned | Calls, declarations and mutation | `call`, `global`, `global_get`, `global_set`, `import_func`, `import_global`, `import_mem`, `import_table`, `local`, `local_set`, `local_tee`, `memory`, `table` |
| Planned | Integer or mixed numeric operations | `clz`, `ctz`, `div_si`, `div_ui`, `eq`, `extend`, `extend_i32_s`, `extend_i32_u`, `ge_si`, `ge_ui`, `gt_si`, `gt_ui`, `le_si`, `le_ui`, `ne`, `popcnt`, `rem_si`, `rem_ui`, `rotl`, `rotr`, `shl`, `shr_s`, `shr_u`, `wrap` |
| Planned | Floating-point operations and conversions | `abs`, `ceil`, `convert_s`, `convert_u`, `copysign`, `demote`, `div`, `floor`, `ge`, `gt`, `le`, `lt`, `max`, `min`, `nearest`, `neg`, `promote`, `reinterpret`, `sqrt`, `trunc`, `trunc_sat_si`, `trunc_sat_ui`, `trunc_si`, `trunc_ui` |

Upstream also defines `ExternRefType`, `FuncRefType`, `LimitType`,
`LocalRefType`, and `TableType`. Only integer parameter references from
`LocalRefType` are represented here. Float, vector and reference operands,
mutable local references, other types and attributes, multi-value returns,
and all nested regions are outside the checked profile.

The Lean implementation is original MIT-licensed code. The reference is
LLVM's TableGen (SPDX `Apache-2.0 WITH LLVM-exception`) at commit
`cc45e189bc99870d26d50c5e3a3d215068e74880`.

| Reference | SHA-256 of pinned source |
| --- | --- |
| [WasmSSAOps.td](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/WasmSSA/IR/WasmSSAOps.td) | `01d2e375389b2f83c4bf1c2898c3cfc4cc32141f39bd90de0665dae89155584b` |
| [WasmSSATypes.td](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/WasmSSA/IR/WasmSSATypes.td) | `c199c6f9b592da38b014f99255c77e740ced39e20e2e75e39f0d0c832e2ae0dc` |

The published reference is generated from TableGen and tracks upstream.
[MLIR WasmSSA reference](https://mlir.llvm.org/docs/Dialects/WasmSSAOps/) ·
[LLVM license at the pin](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/llvm/LICENSE.TXT)

## Translation to WebAssembly Core

`Func.toBody` constructs a `Silmaril.Wasm.Validation.Intrinsic.Body`. Each SSA
binding gets its own Core local after the parameters. Bindings are emitted in
source order, including unused bindings. Operands are loaded into the stack
from their typed slots. Subtraction and less-than load the left operand first.
Less-than emits the Core integer relation with the source signedness. Core
`select` loads the true value, the false value and then the condition, and
carries one explicit integer type annotation. The terminator loads its operand
and emits Core `return`. The local layout must fit the 32-bit local-index space.
`Func.toWasm?` enforces that bound and returns an ordinary `Silmaril.Wasm.Func`
with the supplied type index. The caller supplies the index's signature when
using the function-validation theorem.
[Lowering](../../Silmaril/Wasm/SSA/MLIR/WasmSSA/Defs.lean) ·
[Intrinsic Core syntax](../../Silmaril/Wasm/Validation/Intrinsic/Defs.lean)

| Theorem in `Silmaril.MLIR.WasmSSA` | Checked statement |
| --- | --- |
| `Func.toWasm_exprOk` | The emitted body has Core judgment `ExprOk` with the declared integer result in the function body context. |
| `Func.toWasm_funcOk`, `Func.toWasm?_funcOk` | The emitted function has Core judgment `FuncOk` if the supplied type index resolves to a definition that expands to its signature. |
| `Func.toWasm?_isSome_iff` | The optional lowering succeeds exactly when parameters plus bindings fit the local-index space. |
| `Examples.selectDifference_lowers`, `Examples.selectDifference_validates` | A mixed-width block with reused SSA values lowers to the stated Core instructions and locals, and the function validates at type index zero. |
| `Examples.constantBits_lowers` | An `i32` constant with all bits set retains its bit pattern, and an unused `i64` binding still lowers. |
| `Examples.lessThanSigned_lowers`, `Examples.lessThanUnsigned_lowers` | For either integer width the emitted Core function preserves operand order and signedness and puts the comparison result in an `i32` local. |

[WasmSSA theorem header](../../Silmaril/Wasm/SSA/MLIR/WasmSSA/Thms.lean)

## Returned-word observation

`Func.eval` evaluates the typed source block on integer arguments in
declaration order. Each operation extends the source environment with one word.
Arithmetic wraps to the operand width. Comparisons and `eqz` produce the
`i32` words zero and one. `select` chooses the true value on any nonzero
`i32` condition. The evaluator covers both widths and all 14 checked
mnemonics in their modeled integer forms.
[Source evaluator](../../Silmaril/SSA/MLIR/WasmSSA/Eval/Defs.lean) ·
[Pinned operation definitions](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/WasmSSA/IR/WasmSSAOps.td)

| Theorem in `Silmaril.MLIR.WasmSSA` | Checked statement |
| --- | --- |
| `Func.toWasm_returns` | From `Frame.forCall` with the typed arguments followed by the emitted locals, the actual emitted body can reach Core `return` with exactly the source word on the stack and the original store. `Func.Fits` bounds the number of parameters plus bindings by `2 ^ 32`. |
| `Func.toWasm_invoke` | Given a store entry with the emitted function as its code and a type that expands to the source signature, Core `invoke` can reach that singleton result and the original store. |
| `Examples.selectDifference_returns`, `Examples.selectDifference_equal_returns` | The stated Core body returns the wrapped difference on inputs `5, 9` and the first parameter on inputs `5, 5`. These runs exercise operand order, reuse and both arms of `select`. |

The two correspondence theorems above give an existential run of Core 3.0
`Steps` for every numeric profile and host relation. The body theorem uses
the same observation as WasmSpec's `Computes` with the exact return
configuration. The invocation theorem uses Core Logic's body-to-invocation
theorem. The Wasm SSA checked optimizer concerns a
separate `BFunc` pathway with its own fragment recognition and runtime
certificate.
[Execution theorems](../../Silmaril/Wasm/SSA/MLIR/WasmSSA/Execution/Thms.lean) ·
[WasmSpec statement forms](../../Silmaril/WasmSpec/Common/Defs.lean) ·
[Wasm SSA Core certificate](../../Silmaril/Wasm/SSA/CoreCert/Thms.lean)

## All Core executions

`IntBodyCode` admits administrative values and the flat instructions emitted
by the lowering. Every Core step preserves that fragment and the store, and the
same step is available for every numeric profile and host relation. The
fragment excludes the trap and exception bubbles that make the general
host-free Core theorem a joinability result. The first non-value of a stepping
integer body is a local, integer numeric or parametric instruction, so the
existing Core head-step determinism theorem gives exact successor equality.
[Core determinism](../../Silmaril/Wasm/SingleThreaded/Determinism.lean) ·
[Head-step determinism](../../Silmaril/Wasm/SingleThreaded/Determinism/HeadDet.lean)

| Theorem in `Silmaril.MLIR.WasmSSA` | Checked statement |
| --- | --- |
| `IntBodyCode.step`, `IntBodyCode.step_unique`, `IntBodyCode.steps` | Steps of the flat fragment preserve it and the store, transfer across profiles and hosts, and have a unique successor. |
| `Func.toWasm_intBody` | The actual emitted body belongs to the fragment. |
| `Func.toWasm_body_completes` | From the typed call frame with `Func.Fits`, the body follows a finite deterministic path to an exact one-word Core `return`. |
| `Func.toWasm_return_unique` | Any reachable return has the original store, exactly the encoded `Func.eval` word, and an empty suffix after `return`. |
| `Func.toWasm_invoke_completes` | With the emitted code installed at an address at the declared signature, the invocation follows a finite deterministic path to the singleton result and leaves the store unchanged. |
| `Examples.selectDifference_return_unique` | Every return of the stated subtraction and select body on `5, 9` has result `0xfffffffffffffffc`. |

`CompletesAt` gives reachability, a unique successor at each reachable state
with a step, and a continuation from every reachable state to the stated
endpoint. It also records store preservation at every reachable state and
excludes divergence. Any reachable terminal outcome must be the stated
endpoint, which excludes terminal traps and other stuck outcomes for these
starts. The invocation proof checks entry, label exit and frame exit with the
existing Core inversion lemmas. These results concern Core reduction on the
stated body and installed invocation. They leave whole-module instantiation,
binary execution, engine resource limits and GC outside their scope.
[Execution theorems](../../Silmaril/Wasm/SSA/MLIR/WasmSSA/Execution/Thms.lean) ·
[Core inversion lemmas](../../Silmaril/Wasm/Execution/Core/Inversion/Thms.lean)

## Project-defined WASM-GC-SSA syntax

The extension shares the core WasmSSA operation signatures. It adds two
reference types and four Lean operation forms within the same scoped,
straight-line body. The names in the table are Lean constructors. The extension
has no upstream dialect spelling.

| Constructor | Operand | Result |
| --- | --- | --- |
| `refNullI31` | None | Nullable i31 reference |
| `refIsNull` | Nullable i31 reference | `i32` |
| `refI31` | `i32` | Non-null i31 reference |
| `i31GetU` | Non-null i31 reference | `i32` |

Parameters still have integer types. Extended values can be returned and used
by the listed operations at their exact types. The constructors describe operand
and result syntax only. There is no subtyping, heap, allocation, execution or
garbage collection model or theorem for this extension.
[Extension syntax](../../Silmaril/SSA/MLIR/WasmSSA/GC/Defs.lean)

| Theorem in `Silmaril.MLIR.WasmSSA` | Checked statement |
| --- | --- |
| `GC.project_embed` | Embedding a core block and projecting it yields the identical block in every core binding context. |
| `GC.project_eq_some_iff` | Successful projection is equivalent to the original extended block being the literal embedding of the projected core block. The domain has a core result and an all-core incoming SSA context. |
| `GC.embed_injective` | Equal embeddings imply equal core syntax. |
| `Examples.selectDifference_roundTrip` | The syntax round trip leaves the example's Core lowering identical. |
| `Examples.unusedGC_rejected`, `Examples.i31Use_rejected` | Projection rejects extended bindings even when they are under a core prefix, have an integer-returning consumer, or are unused. |

[GC theorem header](../../Silmaril/SSA/MLIR/WasmSSA/GC/Thms.lean) ·
[Checked examples](../../Silmaril/Wasm/SSA/MLIR/WasmSSA/Examples/Thms.lean)

## Reproduce

```sh
lake build --wfail +Silmaril.Wasm.SSA.MLIR.WasmSSA.Examples.Thms
make check CHECK_TARGETS=+Silmaril.Wasm.SSA.MLIR.WasmSSA.Examples.Thms
```

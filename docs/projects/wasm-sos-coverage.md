# Guarded Wasm SOS correspondence

Each row identifies a checked domain for the native V1, Lime1, and Core relations.
The SOS rules and their native renderings live under
[`Silmaril.Wasm.Institution.Operational`](../../Silmaril/Wasm/Institution/Operational).
Readback starts from a rendered source and allows any native successor or finite
endpoint. The exact store, frame, and instruction list are part of the
reconstructed target. See the linked theorem headers for the host, typing, and
allocation premises.

| Slice | Checked boundary | Remaining cases |
| --- | --- | --- |
| [Integer division](../../Silmaril/Wasm/Institution/Operational/LegacyDivision/Transport/Thms.lean) | Flat signed and unsigned division at each width, including a zero divisor and signed overflow traps. | Other numeric operators and division in structured code. |
| [Numeric locals](../../Silmaril/Wasm/Institution/Operational/Locals/Native/Thms.lean) | Typed flat `local.get`, `local.set`, and `local.tee` with exact local updates. | Uninitialized and nonnumeric Core local slots, globals, and arbitrary structured contexts. |
| [Scalar blocks](../../Silmaril/Wasm/Institution/Operational/Blocks/Native/Thms.lean) and [nested branch exits](../../Silmaril/Wasm/Institution/Operational/BranchExit/Native/Thms.lean) | An isolated scalar block with flat locals and normal exit. A separate guard covers `br 1` followed by `br 0` under two already-entered block labels. | Nested source entry, `br_if`, `br_table`, loop continuations, and Lime1 indexed block parameters and multiple results. |
| [Memory32 queries](../../Silmaril/Wasm/Institution/Operational/MemoryQuery/Native/Thms.lean) and [writes](../../Silmaril/Wasm/Institution/Operational/MemoryWrite/Native/Thms.lean) | Isolated `memory.size`, full-width `i32.load`, and full-width `i32.store` at index zero and static offset zero. The bounds trap preserves the store. | Packed and floating accesses, other offsets, growth, Lime1 bulk operations, and Core memory64 or multiple memories. |
| [Direct-call resolution](../../Silmaril/Wasm/Institution/Operational/CallResolution/Native/Thms.lean) and [typed callee frames](../../Silmaril/Wasm/Institution/Operational/CallFrame/Native/Thms.lean) | Individually checked resolution and resolved invocation of one allocated non-host function. Numeric locals, at most one result, explicit return, fallthrough, and trap propagation. The typed caller keeps its value prefix. | Indirect calls, host contracts and divergence, and composition with caller continuations. |
| [Saved caller continuation](../../Silmaril/Wasm/Institution/Operational/CallContinuation/Native/Thms.lean) | One pending `nop` stays in the caller during a resolved invocation. Return reinstates the caller's value prefix and scalar result before `nop` executes. Trap steps discard the continuation and may discard saved values in several steps. | General instruction suffixes, nested call entry, and caller-side state changes. |

The shared legacy baseline uses the native public Wasm V1 and Lime1 relations.
Lime1-specific multi-value and bulk-memory cases and newer Core features have
separate obligations. Whole-module validity and execution, initialization, host
interaction, divergence, and maximal observations require further correspondence.
See the [native version injections](wasm-version-injections.md) and the
[SpecTec snapshot manifest](../../specs/spectec/manifest.json).

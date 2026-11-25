# Pinned TLA+ source acceptance

The HourClock fixture checks a state predicate and a raw action from the
intact upstream module. The native parser reads both source files. The level
checker processes the complete HourClock tree and its attested library
signature. `Endpoints.lowerState` selects `HCini` and `Endpoints.lowerAction`
selects `HCnxt` by their resolved declaration identities in the same registry.
The fixture supplies their denotations to DataBridge.

## Inputs and library contract

Both files come from the TLA+ commit
`bc1b506bdcad80bb518bf3776a9161c34ff0fc4c`. Paths are relative to
`tlatools/org.lamport.tlatools`.

| Source | SHA-256 |
| --- | --- |
| [test-model/examples/SpecifyingSystems/Liveness/HourClock.tla](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/Liveness/HourClock.tla) | `985903176db4725f9cf25df84ad84dcd53ba94be80d26298b87ec86fbc9b08b3` |
| [src/tla2sany/StandardModules/Naturals.tla](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/Naturals.tla) | `73f2a68412039aa86f37ad08f0d0fef50fa8327d0ad8806f515548c75e9d9d84` |

The harness checks the two public infix declarations in the parsed Naturals
tree. It registers a signature with `..` at member 0 (source unit 11) and
`+` at member 1 (source unit 1). Both have two expression slots, a constant
result floor and two contributing operands up to action level. The same
registry serves level checking and data lowering. Naturals calls its parsed
bodies dummy definitions for tools to override. The fixture admits the
resolved `..` and `+` identities to the tagged data evaluator and uses the
checked integer interval and addition contracts. [Naturals header and declarations](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/Naturals.tla#L2-L35)
· [Level signatures](tla-expression-levels.md#levels-and-signatures)

## Checked scope

| Original HourClock unit | Level | Semantic selection |
| --- | --- | --- |
| 1, `HCini` | State | Checked data denotation and General TLA state formula |
| 2, `HCnxt` | Action | Checked endpoint denotation and General TLA action |
| 3, `HC` | Temporal | Level checked |
| 4, anonymous `THEOREM HC => []HCini` | Temporal | Statement level checked |

The anonymous theorem stays in its original unit with the source's absent
proof. The check covers the statement's level. Temporal denotation of
`HC` and proof of the anonymous theorem are subsequent obligations.

At any instant `i` of any behavior `σ` with fixed rigid valuation `ρ`,
the bridged state formula holds exactly when the `hr` coordinate of
`σ i` is `Value.integer n` for some Lean integer `n` with
`1 ≤ n ∧ n ≤ 12`. This includes the case `hr = Value.integer 1`.
The equation applies to arbitrary tagged values and any fixed adapter policy.
The bridge supplies separate rigid and flexible lookups by declaration
identity. Their name types lift `BindingId` to the tagged carrier's universe.
The proof uses the expanded `HCini` selected from source and the library's
tagged interval membership equation. [DataBridge](tla-data-bridge.md)
· [DataElab](tla-data-elab.md)

For the raw `HCnxt` action, write `hour s` and `hour t` for the `hr` coordinate
at the source and target. The action holds exactly when the target hour
equals the result of the source `IF` expression.

```lean
hour t =
  (if hour s = Value.integer 12 then Value.integer 1
   else Value.add policy.numeric (hour s) (Value.integer 1))
```

Both endpoints share the rigid valuation. The prime reads the target, and
the guard and addition read the source. This equation covers arbitrary
tagged valuations with the adapter's fixed numeric policy. When the source
satisfies `hour s = Value.integer n`, the target is exactly
`Value.integer (if n = 12 then 1 else n + 1)`. The corollary requires only
that the source hour be an integer.

## Running the fixture

```sh
python3 -I tests/semantics/tla-source-acceptance/check.py
```

The driver reuses the native parser fixture driver's revision, download
verification and HourClock hash. It stages both files in a temporary
directory and runs the Lean check with warnings as errors. During elaboration
the check parses, resolves, level-checks and lowers the staged source. The
Lean kernel checks the semantic equations over the emitted terms.
This is a source acceptance result for the pinned fixture and interpretation.
[Driver](../../tests/semantics/tla-source-acceptance/check.py)
· [Lean check](../../tests/semantics/tla-source-acceptance/HourClock.lean)

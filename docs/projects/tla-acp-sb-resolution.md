# Intact ACP_SB resolution

Parse the original bytes, then call `Instances.check [(root, .parsed source [])] root`.
ACP_SB has no EXTENDS or INSTANCE edges and uses no external level signatures.
Keep `checked.registry` and `checked.levels` together when handing off to a lowering
pass. In the original tree, `TypeInv` is at unit 4 and `Init` at unit 7. Both are
nullary state-level operators. Each calls a participant and a coordinator
predicate over the same declared constants and variables. The predicates use
membership, set enumerations, `BOOLEAN`, function sets and record sets. The
record-set fields retain their order, names and `.field i` value paths.

The checker visits all 40 units. The fixture's six state, seventeen action and
fifteen temporal operators match the levels reported by pinned SANY. All
declaration paths and identities in pre-existing forms are stable. The added
temporal cases classify fairness and leads-to syntax. Value lowering, action and
temporal denotation, and proof verification are separate tasks. Fairness still
requires implicit-binding support before replay inside INSTANCE.

[Whole-source regression](../../tests/semantics/tla-resolution/ACP_SB.lean) ·
[Level API](tla-expression-levels.md) ·
[Binding paths](tla-module-resolution.md)

## EXCEPT and lexical `@`

The base uses `.operand 0`. The path to clause `i` appends `.update i`, and
that site is the `BindingId.declared` for its lexical `@`. Its binding has
kind `.oldValue`. An occurrence retains its Surface `.oldValue` node and has
a `referenceAt` entry targeting that identity. Clause RHSs use `.body`, and
index arguments append `.updateComponent j, .argument k` to the clause path.
Literal field selectors remain in the AST. A nested EXCEPT base or index
reads the outer `@`, if present. Its RHS reads its own `@`. An occurrence
outside any RHS reports `.oldValueOutOfScope`.

Follow the expansion in *Specifying Systems* §§16.1.7–16.1.8. Visit clauses in
source order. A clause's selected old value reads the preceding updated base
through its full selector. The level of `@` is the join of the preceding
result and the current selector levels. The new result also joins the RHS
level. Caps of action on the base, index arguments and RHSs follow the pinned
SANY built-in signatures. For evaluator replay, evaluate the base and selectors
with the incoming lexical environment and bind the selected old value under
the clause ID for its RHS. Use the accumulated result for successive clauses,
including overlapping selectors.

Pinned SANY's generator agrees on lexical scope, and pinned TLC selects from
the accumulated result. SANY's `AtNode.levelCheck` gathers the base and earlier
clauses, omitting the current selector from the reported level and dependencies.
For `VARIABLE v` and `P == [[TRUE |-> FALSE] EXCEPT ![v'] = @']`, pinned SANY
accepts `P`. Resolution rejects the prime on the action-level selected value,
as required when expanding the selector into the primed operand. Both checkers
reject `P == [[a |-> FALSE] EXCEPT !.a = v', !.a = @']`.

[*Specifying Systems*, §§16.1.7–16.1.8](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=320) ·
[Pinned SANY scope](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/Generator.java#L4175) ·
[Pinned SANY level rule](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/AtNode.java#L83) ·
[Pinned TLC EXCEPT evaluation](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tlc2/tool/impl/Tool.java#L2300)

## Reproduce

Run from the repository root with the pinned Lean toolchain. The upstream byte
pin is shared with the parser harness at TLA+ revision
`bc1b506bdcad80bb518bf3776a9161c34ff0fc4c`.

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Resolution.Examples \
  +Silmaril.Logic.Temporal.TLA.Resolution.Levels.Examples \
  +Silmaril.Logic.Temporal.TLA.Resolution.Instances.Examples
work=$(mktemp -d)
revision=bc1b506bdcad80bb518bf3776a9161c34ff0fc4c
upstream="https://raw.githubusercontent.com/tlaplus/tlaplus/$revision"
curl -fsSL "$upstream/tlatools/org.lamport.tlatools/test-model/examples/acp/ACP_SB.tla" \
  -o "$work/ACP_SB.tla"
printf '%s  %s\n' a62fedef4725c150efd03f5a864bb607f2f3960686b518792144e1d781c6de89 \
  "$work/ACP_SB.tla" | sha256sum --check
lake env lean -DautoImplicit=false -DwarningAsError=true \
  --run tests/semantics/tla-resolution/ACP_SB.lean "$work/ACP_SB.tla"
```

[Pinned source](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/examples/acp/ACP_SB.tla) ·
[Existing parser harness pin](../../tests/semantics/tla-parser/check.py)

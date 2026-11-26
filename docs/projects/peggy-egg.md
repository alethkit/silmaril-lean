# Checked Egg replay for acyclic partial PEGs

The bridge checks a proposed equality between two programs in the **ranked
loop-free partial PEG fragment**. It uses the typed PEG table and the sorted
Egg explanation judgment. Tate, Stepp, Tatlock and Lerner introduce PEG
sharing and E-PEGs in §2 and give their semantics in Fig. 11. The exact
citation and artifact hash are in the [PEG core notes](peggy.md).

## Input and certificate

1. Build typed tables or pass numeric wiring through
   [`PEG.RawGraph.check`](../../Silmaril/SSA/PEG/Builder.lean). The bridge
   accepts `Graph … 0`, so a label can be a parameter, primitive or φ. Supply
   a rank for each node to
   [`Acyclic.Ranked.check`](../../Silmaril/SSA/Peggy/Acyclic/Defs.lean).
   It checks strict descent at every operand of every node, including
   unreachable rows. Numbering can refer forward. A valid rank is a
   certificate supplied by the caller.
2. [`Bridge.Egg.encodeOutputs`](../../Silmaril/SSA/Peggy/Bridge/Egg/Defs.lean)
   recursively unfolds root references into sorted Egg terms. Parameter
   variables name slots in the ordered input signature. Symbols retain the
   result sort and ordered operand sorts. Each occurrence of a reference to
   a shared producer unfolds to the same term.
3. Supply a table of `Core.Rule`s and one
   [`Core.Replay.Receipt`](../../Silmaril/Logic/Egg/Core/Replay/Defs.lean)
   per output position. Each rewrite refers to a bounded rule index and
   gives a sorted substitution and a receipt per declared guard. The other
   constructors support reflexivity, symmetry, transitivity and congruence.
   Replay checks each instantiated guard's two endpoints, each transitivity
   join and both requested root endpoints structurally.
   Input and result signatures are shared by the two graphs at the type
   level. Pairing is positional, including repeated roots and distinct
   parameters of the same sort. A permutation requires an explicit
   interface adapter. Receipts are typed Lean data. A caller reading foreign
   receipts must first decode the signature, term, sort and index data.
4. `checkOutputs` returns an Egg explanation for each paired result on
   success. The explanations have an empty premise set. The executable
   checker needs decidable equality on dialect sorts and at each primitive
   profile. Sorts, symbols and carriers live in Lean's `Type`, as in the
   current Egg signature. The generic Egg comparator can accept a sound
   partial symbol comparison, which may reject a match.

## Semantics and guarantee

The fragment evaluates each node to an `Option` of its declared carrier,
using Boolean control, natural-number counts and dialect-defined data.
Parameter slots can be undefined. A primitive is a deterministic, pure
partial function of fully defined operands. The evaluator lifts it
strictly in every argument, including unused arguments, and propagates
`none`. A φ yields `none` when its control is undefined and observes only
the selected arm otherwise. The Egg algebra has ordinary total functions
on these option-valued carriers.

[`encode_eval` and `encodeOutputs_eval`](../../Silmaril/SSA/Peggy/Bridge/Egg/Thms.lean)
relate the independent graph denotation to Egg evaluation.
`checkOutputs_sound` proves equality of the entire ordered output vector,
including each result's definedness, for every shared input valuation and
every interpretation satisfying all the supplied rules. Rule satisfaction
quantifies over partial values and assumes each declared guard before the
conclusion. Replay checks rule applications and guard proofs. Establishing
rule satisfaction is a separate obligation of the dialect client. For
example, the fixture proves `φ(c,x,y) = x` under `c = yes()` with
`yes()` interpreted as `some true`. It also proves that unconditional
`φ(c,x,x) = x` can fail when `c` is undefined.

The observation records the ordered partial values. Failure kinds,
evaluation order and count, dead nodes, effects and cost are outside it.
The claim about lazy conditionals concerns their denotation. Unfolding preserves meaning because repeated uses
read the same pure value. The tree representation and replay can repeat
work, with exponential expansion in the number of shared graph nodes.
They carry no sharing or resource bounds.

## Figure 11 correspondence

[`Bridge.Figure11.Thms`](../../Silmaril/SSA/Peggy/Bridge/Figure11/Thms.lean)
relates this bridge to the [guarded native PEG denotation](peg-semantics.md).
The graph rank makes native demands well founded. The adapter retains
every data carrier, relates Bool and Nat to their lifted versions, and
injects each defined Figure 11 input as `some` at the same parameter slot.
It preserves strict primitive application and lazy φ. `denote_eq_valuation` proves exact agreement at every node
by showing that the lifted bridge evaluation solves the native equations
and using their uniqueness. This includes `none` and uses any proof of
well-founded native demands.

`checkOutputs_figure11_sound` applies the existing Egg soundness theorem
to that adapter and proves equality of the actual ordered
`PEG.Graph.observe` tuples. The [root optimizer](peggy-optimizer.md)
composes those checked explanations and uses `outputs_figure11_sound`
for their final endpoints. Rule satisfaction still ranges over all
partial Egg variable valuations, even though Figure 11 takes defined
parameters. The auxiliary bridge can still be used with undefined
parameters. The Figure 11 correspondence is on its defined-input
boundary.

For a candidate in the loop-free fragment, check its wiring and rank,
then bind its actual roots to accepted receipts. For a guarded cyclic
candidate, the [E-PEG certificate kernel](peggy-epeg.md) works directly
with the native streams and the candidate's equations.

## Checks

```sh
lake build --wfail +Silmaril.SSA.PEG.Semantics.Thms +Silmaril.SSA.Peggy.Bridge.Figure11.Thms PEGCoreTests PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker Silmaril.Logic.Egg.Core.Replay.Defs
lake env leanchecker Silmaril.SSA.Peggy.Acyclic.Defs
lake env leanchecker Silmaril.SSA.Peggy.Bridge.Egg.Defs
lake env leanchecker Silmaril.Proofs.SSA.Peggy.Bridge.Egg.Sound
lake env leanchecker Silmaril.SSA.Peggy.Bridge.Egg.Thms
lake env leanchecker Silmaril.SSA.Peggy.Bridge.Figure11.Defs
lake env leanchecker Silmaril.Proofs.SSA.Peggy.Bridge.Figure11.Correspondence
lake env leanchecker Silmaril.SSA.Peggy.Bridge.Figure11.Thms
lake env leanchecker tests.ssa.PeggyEgg
scripts/check-layout.sh
```

The [regression fixture](../../tests/ssa/PeggyEgg.lean) checks replay of a
guarded φ simplification under a primitive with shared operands, rejection
of a wrong guard, a broken transitivity join, swapped roots and a
well-typed cycle, and evaluation with partial inputs and an undefined
unselected arm. The native fixture checks both branch choices and bottom
control directly from the guarded equations, and uses the correspondence
theorem to lift receipt soundness to the whole native observation.
`PeggyEggTests` is included in `make check`.

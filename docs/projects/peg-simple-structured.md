# Compositional SIMPLE to PEG lowering

`Structured.translate` compiles the full typed `Program P true` syntax,
including loops in sequences, branches, and other loops. This is
`Trans-While` composed with the other rules of Figure 17 in Tate, Stepp,
Tatlock and Lerner’s *Equality Saturation: A New Approach to Optimization*.
`Structured.translate_returns` proves the successful-return direction of
Theorem 2 for this syntax. It accepts the existing `Exec` judgment and
the interpretation law for a supplied opcode of profile `[.bool] → .bool`.
The law requires Boolean negation to return the defined negated value.
The ordinary source primitives may be partial. [Paper, §6](https://arxiv.org/pdf/1012.1802v3#page=31) ·
[Source calculus and Coq comparison](peg-simple.md)

## Graph construction and admission

A statement extends a typed node context. Sequencing threads the exit
context into the next statement. Both arms of a branch start from the
same entry context and share one φ guard. A loop reserves one θ per
carried slot, compiles its guard and body over those slots, and connects
the body’s results to the θ feedback operands. All exit slots use eval
with one shared pass on the negated guard. The surrounding statement
receives the complete exit context. [Compiler](../../Silmaril/SSA/PEG/Simple/Structured/Defs.lean)

The numbered graph uses each pass row’s own address as its loop ID.
Distinct pass rows hence have distinct IDs. The forest entry at an inner
pass points to its immediate enclosing pass. The parent address strictly
precedes the child address. The current encoding reserves one coordinate
per vertex, with unused coordinates at rows other than pass; this avoids
a separate renumbering of loop IDs. [Admission proofs](../../Silmaril/Proofs/SSA/PEG/Simple/Structured/Guard.lean)

The compiler emits a checked lexicographic rank. At each address in
increasing order it compares the side of the corresponding vertex cut,
then the counter for that address. Ordinary, θ initial, and eval index
edges advance in vertex order. A sample crosses its pass cut before
reaching the counter that it can reset. Both ends of a feedback edge
follow their own pass, so the decrement is reached before any cut that
could increase. The rank proof covers arbitrary samples, including eval’s
entire prefix, and independently gives well-founded Figure 11 demands.

`Structured.translate_wellFormed` proves structural admission for the
same numbered graph. A loop region is the open interval after its pass
and before the pre-loop table. Each interval’s pass row records its
actual forest parent. The compiler proof tracks which intervals can
contain an input or exit reference. An edge into an interval from
outside it must sample that loop. If a path starts already inside the
target region, the starting loop is that region or its descendant.

An observer cycle crosses the pass cut going forward. A sample
crosses the cut immediately after the pass, and an eval index edge
crosses the cut at the pass. The return crossing must use a feedback
edge whose source lies inside its own loop’s interval and whose target
is after that loop’s pass. These bounds place the observed pass strictly
inside the feedback loop. The interval ancestry proof turns that
containment into a nonempty walk in the actual forest. Together with
forest well-formedness and the feedback-cycle clause, this gives the
`wellFormed` field for Peggy’s `Dialect.OpenGraph` and its equations.
[Public theorems](../../Silmaril/SSA/PEG/Simple/Structured/Thms.lean) ·
[Rank checker and Figure 11 semantics](peg-semantics.md)

## Preservation and observations

At a fragment boundary the proof fixes the enclosing loop coordinates.
Its input and output assertions hold at every index with those
coordinates. For a loop, the induction adds the fresh loop coordinate
to the fixed frame and follows the finite source execution. The θ
initial equations interpret its entry store. The feedback equations and
the induction hypothesis for the body give the next store, even when the
body executes an inner loop. Continuing source guards give defined false
exit samples. The stopping guard produces the first true sample at the
exact source trip count. Every earlier store in that trace supplies the
defined eval samples. The top-level frame is empty, so the observed
successful return holds at every initial index. [Loop proof](../../Silmaril/Proofs/SSA/PEG/Simple/Structured/Loop.lean) ·
[Statement induction](../../Silmaril/Proofs/SSA/PEG/Simple/Structured/Correctness.lean)

The theorem concerns successful returns. The source calculus retains
separate finite failure and divergence observations, while the Figure
11 target keeps one bottom. The regression runs the second sibling loop
inside a branch and gives it the first loop’s result. The nested example
uses the current outer counter as the inner trip count, so an input of
three produces inner runs of three, two, and one steps. Both regressions
check the compiled root with a nonzero initial index and inspect the
generated parent table. A concrete nested cycle traverses the inner eval’s
index edge and its pass sample. The structural theorem yields the outer
loop as the enclosing feedback witness. The fixture also checks existence
and uniqueness of the nested graph’s Figure 11 solution through structural
admission. [Tests](../../tests/ssa/PEGSimple.lean)

## Replay

```sh
lake build --wfail +Silmaril.SSA.PEG.Simple.Structured.Thms PEGCoreTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGSimple.lean
lake env leanchecker Silmaril.SSA.PEG.Simple.Structured.Thms
lake env leanchecker tests.ssa.PEGSimple
make check CHECK_TARGETS='+Silmaril.SSA.PEG.Simple.Structured.Thms PEGCoreTests'
```

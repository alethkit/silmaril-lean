# Automatic lowering of a top-level SIMPLE while

This extends the loop-free frontend with the `Trans-While` construction
from Figures 15 and 17 of Tate, Stepp, Tatlock and Lerner’s *Equality
Saturation: A New Approach to Optimization*. `WhileProgram` represents one
top-level while, followed by a return of a carried slot. Its parameters
are the initial carried store. The guard is a typed expression and the
body can use assignments, projections, sequences and branches. The body
has a fixed input and output signature. `WhileProgram.source` embeds this
fragment into the existing `Program P true` and uses its finite execution
judgment. [Paper, §6](https://arxiv.org/pdf/1012.1802v3#page=31) ·
[Loop-free frontend](peg-simple.md) ·
[Compiler](../../Silmaril/SSA/PEG/Simple/While/Defs.lean)

## Wiring and admission

`WhileProgram.translate` emits a numbered PEG with one loop coordinate.
Each carried slot gets a θ with its parameter as the initial operand
and the corresponding lowered body result as the feedback operand. The
existing loop-free builder lowers the guard and body using the θ slots
as its entry references. The result is an eval of the selected carried
slot at the pass of the negated guard. The compiler takes the typed
Boolean negation opcode explicitly. All other instructions use the
source interpretation without a totality hypothesis.

The guard proof uses the ordering of the rows. The eval, pass and exit
test occupy decreasing phases along demand edges into the loop. Inside
the loop, ordinary and θ initial edges move to higher vertex numbers.
θ feedback decreases the iteration coordinate. The generated
lexicographic rank passes `DemandRank.check` for every compiled graph.
The separate structural proof shows that every cycle contains feedback,
no cycle contains a sampling or index edge, and the single loop is in
scope. Demand well-foundedness covers every sampled index, including
indices greater than the initial request. [Admission proofs](../../Silmaril/Proofs/SSA/PEG/Simple/While/Guard.lean)

## Successful returns

`WhileProgram.translate_returns` takes a successful source execution
and the interpretation law for the supplied negation opcode. It proves
that the unique Figure 11 valuation gives the exact returned value at
the compiled root. `Exec.while_trace` extracts a finite trace with the
exact number of body steps. The θ equations and the loop-free body proof
show that each carried slot has the corresponding source value at each
step. True source guards give a defined false exit test before the exit.
The final false source guard gives the first true exit test. This
establishes the exact pass result. The carried values at all earlier
steps establish the defined prefix for eval. The theorem holds at any
initial observation index because both pass and eval replace the single
loop coordinate when sampling. [Public theorems](../../Silmaril/SSA/PEG/Simple/While/Thms.lean) ·
[Preservation proof](../../Silmaril/Proofs/SSA/PEG/Simple/While/Returns.lean)

The source still distinguishes finite failure from absence of a finite
execution. The PEG observation follows Figure 11 and uses a single
bottom. The theorem concerns successful returns. In particular it
preserves a successful branch when the other arm has a failing
primitive. The fixture also exhibits a finite source failure when that
arm is taken. The factorial tests retain the manually wired graph and
prove the automatic compiler result for every natural accumulator and
counter, with concrete checks at zero and ten iterations.
[Regression fixture](../../tests/ssa/PEGSimple.lean) ·
[Figure 11 conventions](peg-semantics.md)

## Follow-up

Lowering loops inside sequences and branches requires a context-threading
compiler entry and exit for each loop, with distinct loop IDs for sibling
occurrences. Nested loops also require a loop forest and a preservation
invariant indexed by the fixed enclosing coordinates. That invariant must
establish each inner pass and eval prefix and prove that revisiting an
outer iteration changes only the permitted coordinates. Emission of eval
for every live slot belongs at that compositional exit boundary. This
milestone emits an eval for the one observed slot.

## Replay

```sh
lake build --wfail +Silmaril.SSA.PEG.Simple.While.Thms PEGCoreTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGSimple.lean
lake env leanchecker Silmaril.SSA.PEG.Simple.While.Thms
lake env leanchecker tests.ssa.PEGSimple
make check CHECK_TARGETS='+Silmaril.SSA.PEG.Simple.While.Thms PEGCoreTests'
```

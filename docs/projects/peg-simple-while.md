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

## Checked scalar reversion

The inverse checker `Revert.While.extract` takes a typed, numbered
seven-vertex PEG with one loop and one carried result. It reads the unary
continuation test and feedback update, plus the Boolean negation used
by the exit test. It recompiles those primitives using `WhileProgram.translate`
and compares the full serialized table. The comparison checks every sort,
opcode, wire, loop parent and root. The dialect supplies decidable equality
at each opcode profile. Success produces the existing SIMPLE while over
the initial parameter, updating the single carried slot and returning it.
[Extractor](../../Silmaril/SSA/PEG/Simple/Revert/While/Defs.lean)

`Form.compile_extract` proves exact recovery of the three primitive symbols
on the compiler image. `Certificate.compile_eq` proves that recompilation
of any admitted input recovers the same graph. `Certificate.observe_of_returns`
reuses the frontend's successful-return theorem with the meaning of the
negation opcode as its sole primitive-law premise. The proof therefore
covers Figure 11's earliest pass and every earlier eval sample needed
for the successful return. The observation theorem goes from an extracted
SIMPLE return to the input PEG. `Certificate.returns_of_defined` supplies
the reverse direction when the guard and complete body step are total.
[Public theorems](../../Silmaril/SSA/PEG/Simple/Revert/While/Thms.lean)

This is a canonical case of §7.3 with one unnested loop and the existing
compiler's numbering. It checks the exact eval/pass pairing and θ feedback
wire. General Fig. 19 scope and Type-Eval-Pass rules, arbitrary numbering,
multiple carried slots and simultaneous copies, loop fusion, MustEval,
and LICM remain separate obligations. The fixture exercises the extractor,
proves the recovered loop's countdown return at zero and arbitrary finite
iterations, and rejects a sorted table whose pass bypasses the negation.
[Paper §7](https://arxiv.org/pdf/1012.1802v3#page=40) ·
[Regression](../../tests/ssa/PEGCanonicalWhile.lean)

## Simultaneous two-slot reversion

`Revert.While.Pair.extract` accepts the ten-row compiler layout for one
top-level loop with two typed carried slots and one observed result. It
recovers the continuation test, two updates, Boolean negation, and the
return slot. The test and left update read the old left slot. The right
update takes the old left and right slots in order. Either carried slot
can be returned, even when the slot sorts coincide. The finite table
comparator checks the root, pass, θ initialization and feedback, operand
order, and all other rows against the existing compiler.
`Certificate.compile_eq` proves that every accepted table is exactly
recovered by recompilation.
[Extractor](../../Silmaril/SSA/PEG/Simple/Revert/While/Pair/Defs.lean) ·
[Public certificates](../../Silmaril/SSA/PEG/Simple/Revert/While/Pair/Thms.lean)

The generated body assigns the left and right updates to fresh slots
and projects them together into carried order. The right assignment
reads through the new left slot to the old store. The checker synthesizes
this schedule from the recovered opcodes. A well-typed wire that instead
passes the new left value to the right update is rejected. `Form.runFuel`
executes the recovered loop up to the supplied number of body steps.
A successful run gives an execution of the emitted SIMPLE syntax by
`Form.runFuel_returns`. Undefined tests or steps and exhaustion all
produce `none`. The first false guard can be observed with zero fuel.

### From defined PEG returns to a finite SIMPLE trace

`WhileProgram.translate_exitWitness` shows the reverse direction of the
top-level compiler on programs with a total guard and complete body step.
It inverts Figure 11's eval to recover a pass count, the selected sample
at that count, and definedness of every earlier sample of the returned
θ. It inverts pass to obtain the least true exit-test sample, with defined
false samples at all earlier indices. Those samples
guide induction through the SIMPLE loop. Each step advances the full
carried store, so the returned value is the selected θ's value at the
first pass. `Pair.Certificate.exitWitness_of_defined` transports this
proof to accepted tables. `returns_of_defined` gives the successful
SIMPLE return, and `runFuel_of_defined` proves that the pass count is
sufficient fuel for the executable runner. The emitted pair body satisfies the contract when its test
and both update opcodes are total on defined operands and the negation
opcode has its stated meaning.
[Compiler theorem](../../Silmaril/SSA/PEG/Simple/While/Thms.lean)

The regression returns 16 from an initial counter of 3 and accumulator
of 10. Its counterexample uses a defined left result and a partial right
update. The PEG returns zero after one iteration while the emitted SIMPLE
fails in that iteration. This is why the reverse theorem requires
totality of the whole scheduled step, including updates omitted by the
return demand. General table reconstruction, nested loop extraction,
loop fusion and LICM remain separate obligations.
[Regression](../../tests/ssa/PEGCanonicalWhile.lean) ·
[Paper §7.3](https://arxiv.org/pdf/1012.1802v3#page=43)

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
lake build --wfail +Silmaril.SSA.PEG.Simple.Revert.While.Pair.Thms PEGCoreTests PEGCanonicalWhileTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGSimple.lean
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGCanonicalWhile.lean
lake env leanchecker Silmaril.SSA.PEG.Simple.While.Thms
lake env leanchecker tests.ssa.PEGSimple
make check CHECK_TARGETS='+Silmaril.SSA.PEG.Simple.Revert.While.Pair.Thms PEGCoreTests PEGCanonicalWhileTests'
```

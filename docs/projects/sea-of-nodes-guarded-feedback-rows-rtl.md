# Guarded feedback rows in RTL and explicit Φ

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms`.
`checkPlan` admits a typed i64 bank at a supplied width. Entry and copy
indices are zero-based and checked against the full bank. Each computation
reads two old bank slots and writes a fresh temporary. Destinations are
distinct. The guard names one computed producer and its destination.
The checker requires them to agree. The guard compares that producer
with `eq`, `ne`, or signed `slt` against `limit` by default. Set
`guardRhs := some (.arg slot)` to read an old bank slot, or
`guardRhs := some (.output producer 0)` to read a distinct row result.
Exit reads the old `exitSlot` by default. Set
`exitOrigin := some (.output producer 0)` to return a computed result
from that activation. The checker requires that producer's destination
to be `exitSlot`. Positional `Spec` literals take `exitOrigin` followed
by `guardRhs`.
[Guarded pair][pair] · [Row compiler][row] · [Explicit Φ baseline][phi]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing (WordTuple words)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def crossed : Spec where
  entry := [0, 1, 2]
  copies := [0, 1, 0]
  updates := [⟨.sub, 1, 0, 1⟩, ⟨.add, 0, 0, 1⟩]
  guardOrigin := .output 1 0
  guardDestination := 0
  comparison := .ne
  limit := 14
  exitSlot := 2

def sampleInput : WordTuple 3 := .cons (5 : Word) (.cons (2 : Word) (.cons (20 : Word) .nil))

#eval do
  let plan ← checkPlan 3 crossed
  let (rtl, ssa) ← lowerChecked 3 crossed
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let observe (backedges : Nat) :=
    let machine := (rtl.runMain (plan.rtlFuel backedges) 0 (words sampleInput) mem).returnedValues?
    let typed := (Generic.Fuel.run model (inputEnv model sampleInput) (backedges + 1) ssa).bind fun (_, packet) =>
      (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
    (machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)
  pure (observe 1, observe 2)
-- some ((none, none), some [7], some 7)
```

The first two activations feed back `(7, 3, 5)` and `(10, 4, 7)`.
The guard's addition reads old slot 1 even though the subtraction
replaces it, and slot 2 copies old slot 0. The next comparison sees 14
and exit projects the old slot 2, which is 7. Changing the guard origin
to `.output 0 0` is refused because producer 0 writes slot 1.
[Activation regression][regression] · [Whole-loop regression][fuel-regression]

`activation_agrees` proves the guard choice and complete feedback tuple
or exit projection. `incoming_alignment` identifies the actual entry
and feedback branches in either predecessor order. The two orders
recover the same branch terms of the emitted CFG. [Activation theorems][thms]

For a row with `k` computations, `activationSteps` is `k + 3`
with a fixed limit and `k + 2` with an old-bank or computed operand.
Both execute the row, comparison and branch. The fixed limit adds one literal.
A return after `b` backedges needs exactly
`activationSteps * (b + 1) + 2` RTL steps including entry and return,
and `b + 1` λSSA visits. The fixed-limit example needs 17 RTL steps
and 3 λSSA visits.
`runMain_fuel_iff` gives the threshold at arbitrary RTL fuel.
`bounded_returns_iff` and `bounded_absence_iff` compare observation at
the matched budgets. `returns_iff` relates the checked targets' finite
returns with the entire final memory equal to the initial memory.
The proofs cover the current pure single-header i64 bank profile.
[Whole-loop theorems][fuel-thms]

## Return a computed row value

A native loop can name a header producer in its result wire, as the
source swap example does. This add/sub row selects the exit producer
independently of the guard producer. The selection uses the existing
exit successor and introduces no additional machine step.
[Native result wire][native-result]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing (WordTuple words)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def subtractOnExit : Spec where
  entry := [0, 1, 2]
  copies := [0, 1, 2]
  updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 2, 2, 1⟩]
  guardOrigin := .output 0 0
  guardDestination := 0
  comparison := .ne
  limit := 3
  exitSlot := 2
  exitOrigin := some (.output 1 0)

def observe (spec : Spec) (input : WordTuple 3) := do
  let plan ← checkPlan 3 spec
  let (rtl, ssa) ← lowerChecked 3 spec
  let initial := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain (plan.rtlFuel 2) 0 (words input) initial).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model input) 3 ssa).bind
    fun (_, packet) => (Generic.Fuel.decodeArgs model [word] packet).map fun fields =>
      Silmaril.SSA.RVSDG.Tuple.get fields .head
  pure (machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)

#eval observe subtractOnExit (.cons (0 : Word) (.cons (1 : Word) (.cons (10 : Word) .nil)))
-- some (some [7], some 7)

#eval observe { subtractOnExit with limit := 42, guardRhs := some (.arg 2) }
  (.cons (0 : Word) (.cons (1 : Word) (.cons (5 : Word) .nil)))
-- some (some [2], some 2)

#eval observe { subtractOnExit with guardRhs := some (.output 1 0) }
  (.cons (0 : Word) (.cons (1 : Word) (.cons (6 : Word) .nil)))
-- some (some [3], some 3)

def signedCrossing : Spec :=
  { subtractOnExit with
    updates := [⟨.add, 0, 0, 1⟩, ⟨.add, 2, 2, 1⟩]
    comparison := .slt
    guardRhs := some (.output 1 0) }

#eval observe signedCrossing (.cons (-2 : Word) (.cons (1 : Word) (.cons (0x7fff_ffff_ffff_fffe : Word) .nil)))
-- some (some [9223372036854775808], some 9223372036854775808)
```

At `(0, 1, 10)` two backedges lead to old bank `(2, 1, 8)`.
The exit guard sees 3 and returns the freshly computed `8 - 1 = 7`.
An old-slot exit would return 8. With stride zero and counter 1 a
fixed-point proof excludes every finite return in both targets.
Selecting guard producer 0 as the exit origin while retaining
`exitSlot := 2` is refused. `no_finite_return_iff` in
`Rows.Institution.Thms` applies to either exit selection.
[Computed exit regression][computed-regression] · [Observation laws][institution-thms]

## Compare with an old bank slot

The source swap loop's comparison with a runtime input motivates this
two-operand guard. An old bank slot can supply the right operand of
any supported comparison. In the second call above, two backedges lead
to `(2, 1, 3)`. The guard compares the next counter 3 with old slot 2's
value 3. The subtraction has already computed 2 for that slot, and
the exit passes that computed word. The return takes 14 RTL steps and
3 λSSA visits. The checker rejects an out-of-range `.arg` slot for
`guardRhs`. Reindexing the external inputs leaves that bank-local
operand in place. [Native loop example][native-result] · [Operand regressions][operand-regression]

## Compare two row results

Simple's chapter 13 loop regression has a continuation branch that
compares two arithmetic expressions. The last call above uses the same
operand shape with a single `ne` guard over an add and a subtraction.
Both producers read the old bank. At `(2, 1, 4)` the computed words
are both 3, so the loop exits. Using the old value 4 as the RHS would
take the backedge. `guard_compare_computed` identifies the two actual
RTL producer registers. The regression also inspects the emitted λSSA
operands and branch packets, then checks both returns under an external
input swap. A producer outside the update row, a port other than 0,
and reuse of the left producer are refused. [Simple loop branch][simple-two-expressions] · [Operand regressions][operand-regression]

## Signed less-than

Simple's pinned `BoolNode.LT` compares signed Java `long` operands.
For `comparison := .slt`, RTL emits `cmp lts lhs rhs` and λSSA
interprets the typed `WordOp.slt` in the native word model. In
`signedCrossing`, the first comparison is `-1 < 2^63 - 1` and takes
feedback. The next RHS wraps to `-2^63`, so `0 < -2^63` is false and
the computed RHS is returned. Unsigned order or swapped operands
would exit on the first visit. The regression checks both actual
branch packets, the whole memory, and no finite return for a zero
stride. It also checks re-emission after swapping inputs 0 and 1
using `Rows.Reindex.Thms`.
[Simple comparison class][simple-lt] · [Signed guard regression][signed-regression]

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.SignedGuardRegression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.BankOperandRegression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.ComputedExitRegression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Regression
```

[pair]: https://github.com/hiloopai/silmaril-lean/pull/3707
[row]: https://github.com/hiloopai/silmaril-lean/pull/3608
[phi]: https://github.com/hiloopai/silmaril-lean/pull/3631
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Regression.lean
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Thms.lean
[fuel-thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/Thms.lean
[fuel-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/Regression.lean
[computed-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/ComputedExitRegression.lean
[operand-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/BankOperandRegression.lean
[native-result]: ../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/Regression.lean
[institution-thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Institution/Thms.lean
[simple-two-expressions]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter13/src/test/java/com/seaofnodes/simple/Chapter13Test.java#L169-L173
[simple-lt]: https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter13/src/main/java/com/seaofnodes/simple/node/BoolNode.java#L72
[signed-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/SignedGuardRegression.lean

module

import Silmaril.SSA.PEG.Bridge.Theta.Thms
import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Thms
import Silmaril.SSA.Peggy.Bridge.Theta.Thms
import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist.Thms
meta import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist.Defs

namespace Silmaril.SSA.PEG.Bridge.Theta.Tests

open RVSDG (Tuple)

private abbrev Acc : Ty Unit := .data ()

private inductive Instr : InstructionSet.{0,0} Unit
  | stop : Instr [.count, Acc] .bool
  | never : Instr [.count, Acc] .bool
  | bump : Instr [.count, Acc] .count
  | addOldCount : Instr [.count, Acc] Acc

private def values : TotalModel Instr where
  carrier _ := Nat
  run
    | .stop, .cons counter _ => ⟨decide (2 ≤ counter.down)⟩
    | .never, _ => ⟨false⟩
    | .bump, .cons counter _ => ⟨counter.down + 1⟩
    | .addOldCount, .cons counter (.cons sum .nil) => Nat.add sum counter.down + 1

private def loop : Loop Instr .count Acc := ⟨.stop, .bump, .addOldCount⟩

private def form : Form loop.peg := ⟨loop, rfl⟩

private def pair (counter sum : Nat) : Tuple values.toPEG.Value [.count, Acc] :=
  .cons ⟨counter⟩ (.cons sum .nil)

private def idx : Index 1 := fun _ => 0

private theorem firstExit : loop.FirstExit values (pair 0 5) 2 := by
  refine ⟨rfl, fun j hj => ?_⟩
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> rfl

-- Two continue activations. Both updates use the old counter.
example : (compile form).body.run (model values .count Acc) (encodeCarried values (pair 0 5)) =
    RVSDG.Theta.bodyResult (model values .count Acc) true (encodeCarried values (pair 1 6)) := rfl

example : (compile form).body.run (model values .count Acc) (encodeCarried values (pair 1 6)) =
    RVSDG.Theta.bodyResult (model values .count Acc) true (encodeCarried values (pair 2 8)) := rfl

-- Exit returns the old tuple unchanged, rather than feeding back (3, 11).
example : (compile form).body.run (model values .count Acc) (encodeCarried values (pair 2 8)) =
    RVSDG.Theta.bodyResult (model values .count Acc) false (encodeCarried values (pair 2 8)) := rfl

private theorem returned :
    (compile form).Returns (model values .count Acc) (encodeCarried values (pair 0 5))
      (encodeCarried values (pair 2 8)) := by
  apply RVSDG.Theta.Iterate.again (next := encodeCarried values (pair 1 6))
  · rfl
  apply RVSDG.Theta.Iterate.again (next := encodeCarried values (pair 2 8))
  · rfl
  exact RVSDG.Theta.Iterate.stop rfl

example : loop.peg.denote values.toPEG (pair 0 5) loop.demandWellFounded (5, idx) = some ⟨2⟩ :=
  (loop.pass_eq_some_iff values (pair 0 5) idx 2 loop.demandWellFounded).mpr firstExit

example : loop.peg.observe values.toPEG
    (loop.peg.denote values.toPEG (pair 0 5) loop.demandWellFounded) idx =
      (pair 2 8).map (fun _ => some) :=
  (returns_iff_observe values (pair 0 5) form idx loop.demandWellFounded (pair 2 8)).mp returned

example : (compile form).denotePart (model values .count Acc) (encodeCarried values (pair 0 5)) =
    Part.some (RVSDG.Categorical.pack (encodeCarried values (pair 2 8))) :=
  (compile form).denotePart_eq_some (model values .count Acc) _ _ |>.mpr returned

-- Entering already at the stopping bound still executes one body activation.
example : (compile form).Returns (model values .count Acc) (encodeCarried values (pair 2 99))
    (encodeCarried values (pair 2 99)) :=
  RVSDG.Theta.Iterate.stop rfl

private def noExit : Loop Instr .count Acc := ⟨.never, .bump, .addOldCount⟩

example (output : Tuple values.toPEG.Value [.count, Acc]) :
    ¬ noExit.toTheta.Returns (model values .count Acc) (encodeCarried values (pair 0 5))
      (encodeCarried values output) := by
  intro h
  obtain ⟨k, first, _⟩ := (noExit.returns_iff_firstExit values (pair 0 5) output).mp h
  have impossible : false = true := first.1
  contradiction

end Silmaril.SSA.PEG.Bridge.Theta.Tests

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.Tests

open RVSDG (Port Tuple)
open Simple.Revert.While.Region (Certificate Descriptor)

private abbrev num : Ty Unit := .data ()
private abbrev carried : List (Ty Unit) := [.count, num, num]

private inductive Op : InstructionSet Unit
  | pred : Op [.count] .count
  | nonzero : Op [.count] .bool
  | not : Op [.bool] .bool
  | add : Op [num, num] num
  | addAlt : Op [num, num] num
  deriving DecidableEq

private def total : TotalModel Op where
  carrier _ := Nat
  run
    | .pred, .cons c .nil => ⟨c.down - 1⟩
    | .nonzero, .cons c .nil => ⟨c.down != 0⟩
    | .not, .cons b .nil => ⟨!b.down⟩
    | .add, .cons a (.cons b .nil) => Nat.add a b
    | .addAlt, .cons a (.cons b .nil) => Nat.succ (Nat.add a b)

private def sorts (i : Fin 16) : Ty Unit :=
  match i.val with
  | 1 | 2 | 8 | 9 | 12 | 14 => .count
  | 5 | 6 => .bool
  | _ => num

-- Parameters, θs, test and updates are interleaved. The next first
-- accumulator is the old second one, which also feeds the sum.
private def bundledGraph : Graph Op carried carried 16 1 where
  forest := ⟨fun _ => none⟩
  sort := sorts
  node
    | 0 => .ofLabel (.op .add) (.cons ⟨7, rfl⟩ (.cons ⟨3, rfl⟩ .nil))
    | 1 => .ofLabel (.theta 0) (.cons ⟨9, rfl⟩ (.cons ⟨8, rfl⟩ .nil))
    | 2 => .ofLabel (.pass 0) (.cons ⟨6, rfl⟩ .nil)
    | 3 => .ofLabel (.theta 0) (.cons ⟨10, rfl⟩ (.cons ⟨0, rfl⟩ .nil))
    | 4 => .ofLabel (.eval 0) (.cons ⟨3, rfl⟩ (.cons ⟨2, rfl⟩ .nil))
    | 5 => .ofLabel (.op .nonzero) (.cons ⟨1, rfl⟩ .nil)
    | 6 => .ofLabel (.op .not) (.cons ⟨5, rfl⟩ .nil)
    | 7 => .ofLabel (.theta 0) (.cons ⟨11, rfl⟩ (.cons ⟨3, rfl⟩ .nil))
    | 8 => .ofLabel (.op .pred) (.cons ⟨1, rfl⟩ .nil)
    | 9 => .ofLabel (.param .head) .nil
    | 10 => .ofLabel (.param (.tail (.tail .head))) .nil
    | 11 => .ofLabel (.param (.tail .head)) .nil
    | 12 => .ofLabel (.eval 0) (.cons ⟨1, rfl⟩ (.cons ⟨2, rfl⟩ .nil))
    | 13 => .ofLabel (.eval 0) (.cons ⟨7, rfl⟩ (.cons ⟨2, rfl⟩ .nil))
    | 14 => .ofLabel (.pass 0) (.cons ⟨6, rfl⟩ .nil)
    | 15 => .ofLabel (.eval 0) (.cons ⟨7, rfl⟩ (.cons ⟨14, rfl⟩ .nil))
    | ⟨i + 16, h⟩ => False.elim (by omega)
  roots := .cons ⟨12, rfl⟩ (.cons ⟨13, rfl⟩ (.cons ⟨4, rfl⟩ .nil))

private abbrev anchor : Port carried num := .tail (.tail .head)
private abbrev graph := Ordered.scalarView bundledGraph anchor

private def descriptor : Descriptor graph where
  theta := .cons ⟨1, rfl⟩ (.cons ⟨7, rfl⟩ (.cons ⟨3, rfl⟩ .nil))
  initial := .cons ⟨9, rfl⟩ (.cons ⟨11, rfl⟩ (.cons ⟨10, rfl⟩ .nil))
  next := .cons ⟨8, rfl⟩ (.cons ⟨3, rfl⟩ (.cons ⟨0, rfl⟩ .nil))
  guard := ⟨5, rfl⟩
  negated := ⟨6, rfl⟩
  negate := .not
  pass := ⟨2, rfl⟩
  returnSlot := .tail (.tail .head)

private def rank : DemandRank 16 1 :=
  [.phase (fun i => match i.val with
    | 4 | 12 | 13 | 15 => 2
    | 2 | 14 => 1
    | _ => 0), .counter 0,
    .phase (fun i => match i.val with
      | 6 => 3
      | 0 | 5 | 8 => 2
      | 1 | 3 | 7 => 1
      | _ => 0)]

private def cert : Certificate graph where
  descriptor := descriptor
  boundary :=
    { parentless := rfl
      initialRow := fun
        | _, .head | _, .tail .head | _, .tail (.tail .head) => rfl
      thetaRow := fun
        | _, .head | _, .tail .head | _, .tail (.tail .head) => rfl
      negationRow := rfl
      passRow := rfl
      evalRow := rfl }
  rank := rank
  ranked := by decide
  guard :=
    .bind 5 .nonzero _ (by decide) rfl (.cons .head rfl .nil) <|
      .done (.cons .head rfl (.cons (.tail .head) rfl
        (.cons (.tail (.tail .head)) rfl (.cons (.tail (.tail (.tail .head))) rfl .nil))))
  update :=
    .bind 8 .pred _ (by decide) rfl (.cons .head rfl .nil) <|
    .bind 0 .add _ (by decide) rfl (.cons (.tail (.tail .head)) rfl
      (.cons (.tail (.tail (.tail .head))) rfl .nil)) <|
    .done (.cons (.tail .head) rfl (.cons (.tail (.tail (.tail (.tail .head)))) rfl
      (.cons .head rfl .nil)))

private def store (n a b : Nat) : Tuple total.toPEG.Value carried :=
  .cons ⟨n⟩ (.cons a (.cons b .nil))

private abbrev lowered := Region.compile cert
private abbrev values := Region.model total
private abbrev entry (n a b : Nat) := encode total (store n a b)

-- Reading the new first accumulator in the sum would give 2, not 11.
example : lowered.body.run values (entry 2 10 1) =
    RVSDG.Theta.bodyResult values true (entry 1 1 11) := rfl

example : lowered.body.run values (entry 1 1 11) =
    RVSDG.Theta.bodyResult values true (entry 0 11 12) := rfl

example : lowered.body.run values (entry 0 11 12) =
    RVSDG.Theta.bodyResult values false (entry 0 11 12) := rfl

private theorem returned : lowered.Returns values (entry 2 10 1) (entry 0 11 12) := by
  apply RVSDG.Theta.Iterate.again (next := entry 1 1 11) rfl
  apply RVSDG.Theta.Iterate.again (next := entry 0 11 12) rfl
  exact RVSDG.Theta.Iterate.stop rfl

example : lowered.Returns values (entry 0 10 1) (entry 0 10 1) :=
  RVSDG.Theta.Iterate.stop rfl

example (idx : Index 1) : graph.observe total.toPEG
    (graph.denote total.toPEG (store 2 10 1) cert.demandWellFounded) idx =
    .cons (some (12 : Nat)) .nil :=
  (Region.returns_iff_observe cert total (store 2 10 1) (fun _ => rfl) idx (12 : Nat)).mp
    ⟨store 0 11 12, returned, rfl⟩

private def bundle : Ordered.Bundle bundledGraph anchor :=
  (Ordered.check bundledGraph anchor cert).get (by decide)

private theorem observedTuple (idx : Index 1) : bundledGraph.observe total.toPEG
    (bundledGraph.denote total.toPEG (store 2 10 1) bundle.demandWellFounded) idx =
      (store 0 11 12).map (fun _ => some) :=
  (bundle.returns_iff_observe total (store 2 10 1) (fun _ => rfl) idx (store 0 11 12)).mp returned

example (idx : Index 1) : bundle.compile.Returns values (entry 2 10 1) (entry 0 11 12) :=
  (bundle.returns_iff_observe total (store 2 10 1) (fun _ => rfl) idx (store 0 11 12)).mpr
    (observedTuple idx)

-- Row 15 is well typed and uses the same sampled slot, but names another pass row.
private def wrongPass : Graph Op carried carried 16 1 :=
  bundledGraph.withRoots (.cons ⟨12, rfl⟩ (.cons ⟨15, rfl⟩ (.cons ⟨4, rfl⟩ .nil)))

example : (Ordered.check wrongPass anchor cert).isNone = true := by decide

-- Repeating the last eval root puts a same-sort value in the wrong output slot.
private def wrongSlot : Graph Op carried carried 16 1 :=
  bundledGraph.withRoots (.cons ⟨12, rfl⟩ (.cons ⟨4, rfl⟩ (.cons ⟨4, rfl⟩ .nil)))

example : (Ordered.check wrongSlot anchor cert).isNone = true := by decide

open CategoryTheory
open Silmaril.SSA.Peggy.Bridge.Theta
  (Model Side opMap thetaModel peggyToTheta restrictThetaModels)

private def markedSignature : Peggy.Bridge.Theta.Signature Unit := ⟨⟨Op⟩, .not⟩

private def rename : markedSignature ⟶ markedSignature :=
  ⟨Silmaril.SSA.Peggy.Dialect.FixedSortSignature.ofOpcodeMap (fun
    | .pred => .pred
    | .nonzero => .nonzero
    | .not => .not
    | .add | .addAlt => .addAlt), rfl⟩

private def markedModel : Model markedSignature := ⟨total, fun _ => rfl⟩

private def side : Side markedSignature carried := Side.ofBundle bundle rfl

private def equation : Peggy.Bridge.Theta.Equation markedSignature := ⟨carried, side, side.map rename⟩

private abbrev renamed := (Relabel.bundle (opMap rename) bundle).compile

-- The replacement opcode adds one to the second accumulator at each step.
private theorem renamedFirst : renamed.body.run values (entry 2 10 1) =
    RVSDG.Theta.bodyResult values true (entry 1 1 12) := rfl

private theorem renamedSecond : renamed.body.run values (entry 1 1 12) =
    RVSDG.Theta.bodyResult values true (entry 0 12 14) := rfl

private theorem renamedStop : renamed.body.run values (entry 0 12 14) =
    RVSDG.Theta.bodyResult values false (entry 0 12 14) := rfl

private theorem renamedReturns : renamed.Returns values (entry 2 10 1) (entry 0 12 14) :=
  RVSDG.Theta.Iterate.again renamedFirst
    (RVSDG.Theta.Iterate.again renamedSecond (RVSDG.Theta.Iterate.stop renamedStop))

-- The model distinguishes the two sides before identifying the opcodes.
example : ¬ equation.Holds markedModel := by
  intro holds
  let idx : Index 1 := fun _ => 0
  have old := observedTuple idx
  have replaced := ((Relabel.bundle (opMap rename) bundle).returns_iff_observe total
    (store 2 10 1) (fun _ => rfl) idx (store 0 12 14)).mp renamedReturns
  have fromEquation := (holds (store 2 10 1) idx (store 0 11 12)).mp old
  have mismatch : (store 0 12 14).map (fun _ => some) = (store 0 11 12).map (fun _ => some) :=
    replaced.symm.trans fromEquation
  have impossible : some (14 : Nat) = some 12 :=
    congrArg (fun xs => xs.get anchor) mismatch
  contradiction

example : (equation.map rename).translate =
    equation.translate.map (Relabel.opcode (opMap rename)) :=
  equation.translate_map rename

example : (equation.map rename).translate.Holds (thetaModel markedModel) ↔
    (equation.map rename).Holds markedModel :=
  Silmaril.Logic.Institution.Inst.CoHom.satisfaction (peggyToTheta Unit) markedSignature
    (Discrete.mk markedModel) (equation.map rename)

example :
    ((restrictThetaModels Unit).ρ.app markedSignature).mod.obj (Discrete.mk markedModel) =
      Discrete.mk (thetaModel markedModel) := rfl

open RVSDG.LambdaSSA.Theta

private abbrev packet (n a b : Nat) := Operational.pack values (entry n a b)
private abbrev ssaEnv (n a b : Nat) := Operational.inputEnv values (entry n a b)

example : (Region.LambdaSSA.lower bundle).HasType
    [Region.LambdaSSA.Packet carried] [Region.LambdaSSA.Packet carried] :=
  Region.LambdaSSA.lower_hasType bundle

-- Exercise an actual branch to the local header label with the new packet.
example : Isotope.LambdaSSA.Semantics.Region.Eval (Operational.instruction values)
    (Isotope.LambdaSSA.Semantics.extend (ssaEnv 2 10 1) (packet 2 10 1))
    (RVSDG.LambdaSSA.Theta.block (Operational.step bundle.compile).op)
    (7 : Nat) 0 (packet 1 1 11) 7 :=
  Operational.block_eval values bundle.compile _ (entry 2 10 1) (entry 1 1 11) true rfl 7

private theorem ssaReturns :
    Isotope.LambdaSSA.Semantics.Region.Eval (Operational.instruction values) (ssaEnv 2 10 1)
      (Region.LambdaSSA.lower bundle) (7 : Nat) 0 (packet 0 11 12) 7 :=
  (Operational.lower_eval_iff values bundle.compile (entry 2 10 1) 7 7 0 _).mpr
    ⟨entry 0 11 12, returned, rfl, rfl, rfl⟩

example (idx : Index 1) : ∃ (k : Nat) (final : Tuple total.toPEG.Value (.bool :: carried)),
    carriedValues final = store 0 11 12 ∧
    bundle.scalar.TraceObservation total.toPEG
      (bundledGraph.denote total.toPEG (store 2 10 1) bundle.demandWellFounded) idx k final :=
  Region.LambdaSSA.firstExit_of_eval bundle total (store 2 10 1) (fun _ => rfl) idx (store 0 11 12) 7
    ssaReturns

example (idx : Index 1) :
    Isotope.LambdaSSA.Semantics.Region.Eval (Operational.instruction values) (ssaEnv 2 10 1)
      (Region.LambdaSSA.lower bundle) (7 : Nat) 0 (packet 0 11 12) 7 :=
  (Region.LambdaSSA.lower_eval_iff bundle total (store 2 10 1) (fun _ => rfl) idx 7 7 0 _).mpr
    ⟨store 0 11 12, observedTuple idx, rfl, rfl, rfl⟩

-- Already false: the header executes once and exits without a backedge.
example : Isotope.LambdaSSA.Semantics.Region.Eval (Operational.instruction values) (ssaEnv 0 10 1)
    (Region.LambdaSSA.lower bundle) (7 : Nat) 0 (packet 0 10 1) 7 :=
  (Operational.eval_iff_runFuel values bundle.compile (entry 0 10 1) (entry 0 10 1) 7).mpr ⟨1, rfl⟩

example (idx : Index 1) : bundledGraph.observe total.toPEG
    (bundledGraph.denote total.toPEG (store 0 10 1) bundle.demandWellFounded) idx =
      (store 0 10 1).map (fun _ => some) :=
  (Region.LambdaSSA.exists_runFuel_iff_observe bundle total (store 0 10 1) (fun _ => rfl) idx
    (store 0 10 1)).mp ⟨1, rfl⟩

private def runPacket (fuel n a b : Nat) : Option (Nat × Nat × Nat) :=
  (Region.LambdaSSA.runFuel bundle total fuel (store n a b)).map fun
    | .cons count (.cons left (.cons right .nil)) => (count.down, left, right)

set_option interpreter.prefer_native false in
/-- info: (none, some (0, 11, 12), some (0, 10, 1)) -/
#guard_msgs in
#eval (runPacket 2 2 10 1, runPacket 3 2 10 1, runPacket 1 0 10 1)

end Silmaril.SSA.PEG.Bridge.Theta.Region.Tests

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist.Tests

open RVSDG (Tuple)

private inductive Op : InstructionSet Unit where
  | nonzero : Op [.count] .bool
  | not : Op [.bool] .bool
  | stepSize : Op [.count] .count
  | subtract : Op [.count, .count] .count
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .nonzero, .cons n .nil => some ⟨n.down != 0⟩
    | .not, .cons b .nil => some ⟨!b.down⟩
    | .stepSize, .cons size .nil => if size.down = 0 then none else some size
    | .subtract, .cons n (.cons size .nil) => some ⟨n.down - size.down⟩

private abbrev inputs : List (Ty Unit) := [.count, .count]

private def sort : Fin 9 → Ty Unit
  | 4 | 5 => .bool
  | _ => .count

private def raw : RawGraph Op inputs [.count] 9 1 where
  forest := ⟨fun _ => none⟩
  sort := sort
  node
    | 0 => ⟨_, .eval 0, [3, 6]⟩
    | 1 => ⟨_, .param .head, []⟩
    | 2 => ⟨_, .param (.tail .head), []⟩
    | 3 => ⟨_, .theta 0, [1, 8]⟩
    | 4 => ⟨_, .op .nonzero, [3]⟩
    | 5 => ⟨_, .op .not, [4]⟩
    | 6 => ⟨_, .pass 0, [5]⟩
    | 7 => ⟨_, .op .stepSize, [2]⟩
    | 8 => ⟨_, .op .subtract, [3, 7]⟩
  roots := [0]

private def graph : Graph Op inputs [.count] 9 1 := raw.check.get (by decide)

private def descriptor : Descriptor graph where
  theta := .cons ⟨3, rfl⟩ (.cons ⟨2, rfl⟩ .nil)
  initial := .cons ⟨1, rfl⟩ (.cons ⟨2, rfl⟩ .nil)
  next := .cons ⟨8, rfl⟩ (.cons ⟨2, rfl⟩ .nil)
  guard := ⟨4, rfl⟩
  negated := ⟨5, rfl⟩
  negate := .not
  pass := ⟨6, rfl⟩
  returnSlot := .head

private def accepted := check graph descriptor 7

private def input (n size : Nat) : Tuple model.Value inputs := .cons ⟨n⟩ (.cons ⟨size⟩ .nil)

private def run (fuel n size : Nat) : Option (Nat × Nat) := do
  let a ← accepted
  let original ← a.base.runFuel model fuel (input n size)
  let cached ← a.runFuel model fuel (input n size)
  return (original.down, cached.down)

private def sizeCalls {loops : Bool} {vars outs : List (Ty Unit)} :
    Stmt Op loops vars outs → Nat
  | .assign (.op .stepSize _) => 1
  | .assign _ | .project _ => 0
  | .seq a b | .branch _ a b => sizeCalls a + sizeCalls b
  | .while _ _ body => sizeCalls body

private def shape : Option (Nat × Nat × Nat × Nat) :=
  accepted.map fun a =>
    (sizeCalls a.guard.lower, sizeCalls a.initialize, sizeCalls a.body, sizeCalls a.revert.body)

private def zeroTripSkipsUndefined : Bool :=
  (accepted.map fun a => (a.initialize.runLoopFree model (.cons ⟨false⟩ (input 0 0))).isNone)
    |>.getD false

set_option interpreter.prefer_native false

-- The guard reads the changing counter. The invariant input is the unmodified size.
/-- info: (some (0, 1, 0, 1), true) -/
#guard_msgs in
#eval (shape, (check graph descriptor 8).isNone)

/-- info: (some (0, 0), none) -/
#guard_msgs in
#eval (run 4 8 2, run 3 8 2)

-- Unconditionally executing the initializer on the zero-trip input would fail.
/-- info: (true, some (0, 0), none) -/
#guard_msgs in
#eval (zeroTripSkipsUndefined, run 0 0 0, run 1 1 0)

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist.Tests

module

import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.Raw.SSA.Isotope.Semantics.Model

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Tests

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (iter)
open TwoBlock.TwoExit (callCase)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private abbrev Ty := Silmaril.Ty Unit
private abbrev number : Ty := .base ()
private abbrev pair : Ty := .product number number
private abbrev Value := Silmaril.Ty.denote (fun _ : Unit => Nat)
private abbrev Runtime := StateT (List Nat) Part

private inductive Op | header | outer | inner | innerLeft | innerRight | outerRight | join

local instance : HasTy Op Ty :=
  ⟨(fun
    | .header | .outer | .inner | .innerRight => number
    | .innerLeft | .outerRight | .join => pair),
   (fun
    | .header => .coprod number number
    | .outer => .coprod number pair
    | .inner => .coprod pair number
    | .innerLeft | .innerRight | .outerRight => pair
    | .join => .coprod pair number)⟩

private def valueCoe {A B : Ty} : Isotope.Ty.Subty A B → Value A → Value B
  | .refl _ => id
  | .trans f g => valueCoe g ∘ valueCoe f
  | .product f g => fun (a, b) => (valueCoe f a, valueCoe g b)
  | .coprod f g => Sum.map (valueCoe f) (valueCoe g)
  | .empty _ => PEmpty.elim
  | .unit _ => fun _ => PUnit.unit

local instance : TypeModel Ty where
  interp := Value
  productEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun x => by cases x; rfl, fun x => by cases x; rfl⟩
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, fun x => PEmpty.elim x, fun x => Empty.elim x⟩
  coe := valueCoe

local instance : HasEff Op Bool := ⟨fun _ => true⟩

private def instruction : (op : Op) → Value (instrSrc op) → Runtime (Value (instrTrg op))
  | .header, input => StateT.mk fun state =>
    let n : Nat := input
    Part.some (if n = 0 then .inl state.length else .inr n, state ++ [1])
  | .outer, input => StateT.mk fun state =>
    let n : Nat := input
    Part.some (if n = 2 ∨ n = 3 then .inl n else .inr (n, state.length), state ++ [2])
  | .inner, input => StateT.mk fun state =>
    let n : Nat := input
    Part.some (if n = 2 then .inl (n, (40 : Nat)) else .inr n, state ++ [3])
  | .innerLeft, (n, seen) => StateT.mk fun state =>
    Part.some ((n, Nat.succ seen), state ++ [4])
  | .innerRight, _ => StateT.mk fun _ => Part.none
  | .outerRight, (n, captured) => StateT.mk fun state =>
    let seen : Nat := captured
    Part.some ((n, seen + state.length), state ++ [5])
  | .join, (n, captured) => StateT.mk fun state =>
    let seen : Nat := captured
    Part.some (if seen = 41 ∧ state.length = 4 then .inr (1 : Nat) else .inl (n, seen + 1), state ++ [6])

local instance : InstructionModel Op Ty Bool Runtime where
  denote := instruction
  denotePure _ h := False.elim (by change true = false at h; cases h)
  denote_pure _ h _ := False.elim (by change true = false at h; cases h)

private theorem call_run {X Y : Ty} (p : TwoBlock.Instruction Op X Y) (input : Value X) :
    TwoBlock.call (ε := Bool) (m := Runtime) p input =
      p.output ▸ instruction p.op (p.input.symm ▸ input) := by
  obtain ⟨op, src, dst⟩ := p
  subst X
  subst Y
  unfold TwoBlock.call
  change instruction op input >>= pure = instruction op input
  exact bind_pure _

private theorem callCase_run {X L R : Ty} (p : TwoBlock.Instruction Op X (Silmaril.coprod L R))
    (input : Value X) :
    callCase (ε := Bool) (m := Runtime) p input =
      (show Runtime (Value (Silmaril.coprod L R)) from p.output ▸ instruction p.op (p.input.symm ▸ input)) := by
  unfold callCase
  rw [call_run]
  change (_ : Runtime (Value L ⊕ Value R)) >>= pure = _
  exact bind_pure _

private def nested : Body Op number pair :=
  .choice ⟨.outer, rfl, rfl⟩
    (.choice ⟨.inner, rfl, rfl⟩ (.instruction ⟨.innerLeft, rfl, rfl⟩)
      (.instruction ⟨.innerRight, rfl, rfl⟩))
    (.instruction ⟨.outerRight, rfl, rfl⟩)

private def spec : Loop Op number number pair number pair :=
  ⟨⟨.header, rfl, rfl⟩, nested, ⟨.join, rfl, rfl⟩⟩

private def lowered := elaborate spec
private def afterFeedback : List Nat := [1,2,3,4,6]
private def finalToken : List Nat := [1,2,3,4,6,1,2,5,6]
private def joinExit : LabelDen [number,pair] := .inr (.inl ((1 : Nat), (14 : Nat)))
private def headerExit : LabelDen [number,pair] := .inl (0 : Nat)

private abbrev Step := LabelDen [number,pair] ⊕ Nat

private def activation : Nat → Runtime Step := round (ε := Bool) spec

private theorem feedback :
    Elgot.StateT.body activation (2, []) = Part.some (.inr (1, afterFeedback)) := by
  simp [Elgot.StateT.body, activation, round, spec, nested, bodyAction, callCase_run, call_run,
    instruction, afterFeedback,
    StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some,
    Elgot.StateT.distribute, Function.comp_def]

private theorem done :
    Elgot.StateT.body activation (1, afterFeedback) = Part.some (.inl (joinExit, finalToken)) := by
  simp [Elgot.StateT.body, activation, round, spec, nested, bodyAction, callCase_run, call_run,
    instruction, afterFeedback, joinExit, finalToken,
    StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some,
    Elgot.StateT.distribute, Function.comp_def]
  rfl

private theorem skipped :
    Elgot.StateT.body activation (0, []) = Part.some (.inl (headerExit, [1])) := by
  simp [Elgot.StateT.body, activation, round, spec, headerExit, callCase_run, instruction,
    StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some,
    Elgot.StateT.distribute, Function.comp_def]

private theorem undefined : Elgot.StateT.body activation (3, []) = Part.none := by
  simp [Elgot.StateT.body, activation, round, spec, nested, bodyAction, callCase_run, call_run,
    instruction,
    StateT.run_bind, Part.bind_eq_bind, Part.bind_some, Part.bind_none]

private theorem feedbackRun : (iter activation 2).run [] = Part.some (joinExit, finalToken) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  exact .more (by rw [feedback]; exact Part.mem_some_iff.mpr rfl)
    (.done (by rw [done]; exact Part.mem_some_iff.mpr rfl))

private theorem headerRun : (iter activation 0).run [] = Part.some (headerExit, [1]) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  exact .done (by rw [skipped]; exact Part.mem_some_iff.mpr rfl)

private theorem undefinedRun : (iter activation 3).run [] = Part.none := by
  rw [Elgot.StateT.run_iter, Part.eq_none_iff]
  intro output existsReturn
  rw [Elgot.Part.mem_iter_iff] at existsReturn
  cases existsReturn with
  | done h => simp [undefined] at h
  | more h _ => simp [undefined] at h

-- The selected nested arm feeds back. The second activation observes the first
-- activation's token length, selects the other outer arm and exits at the join.
private theorem wireFeedback :
    observe (ε := Bool) lowered.1 (2 : Nat) [] = Part.some (exitTuple (joinExit, finalToken)) := by
  change observe (ε := Bool) (graph spec) (2 : Nat) [] = _
  rw [graph_observe]
  change Part.map _ ((iter activation 2).run []) = _
  rw [feedbackRun]
  rfl

example : observe (ε := Bool) lowered.1 (0 : Nat) [] = Part.some (exitTuple (headerExit, [1])) := by
  change observe (ε := Bool) (graph spec) (0 : Nat) [] = _
  rw [graph_observe]
  change Part.map _ ((iter activation 0).run []) = _
  rw [headerRun]
  rfl

private theorem wireUndefined : observe (ε := Bool) (σ := List Nat) lowered.1 (3 : Nat) [] = Part.none := by
  change observe (ε := Bool) (graph spec) (3 : Nat) [] = _
  rw [graph_observe]
  change Part.map _ ((iter activation 3).run []) = _
  rw [undefinedRun, Part.map_none]

private abbrev Coherent := RegionCoherent (τ := Ty) (Φ := Op) (ε := Bool) (m := Runtime)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) lowered.2.typing (PUnit.unit, (2 : Nat))).run [] =
      Part.some (joinExit, finalToken) := by
  apply (lowered.2.region_returns_iff coherent (PUnit.unit, (2 : Nat)) joinExit [] finalToken).mp
  exact (NestedTheta.Partial.observe_eq_some _ _ _ _).mp wireFeedback

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) lowered.2.typing (PUnit.unit, (3 : Nat))).run [] =
      Part.none :=
  (lowered.2.region_undefined_iff coherent (PUnit.unit, (3 : Nat)) []).mp wireUndefined

section Reverse

open OrderedTheta (carried carriedData resultData)
open OrderedRuntime.Structured (Threaded runtimePort nextRuntime)
open TwoBlock.TwoExit (Carrier ExitCode Pure Route headerPorts armPorts)
open TwoBlock.ExplicitRuntime.Skeleton (Closed)
open LinearChain.Wiring (newest)

private noncomputable def recovered := Reverse.raise (Reverse.canonical spec)

example : recovered.1 = region spec := Reverse.raise_canonical_source spec

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recovered.2.typing (PUnit.unit, (2 : Nat))).run [] =
      Part.some (joinExit, finalToken) := by
  apply (Reverse.raise_returns_iff (Reverse.canonical spec) coherent
    (PUnit.unit, (2 : Nat)) joinExit [] finalToken).mp
  exact (NestedTheta.Partial.observe_eq_some _ _ _ _).mp wireFeedback

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recovered.2.typing (PUnit.unit, (3 : Nat))).run [] =
      Part.none :=
  (Reverse.raise_undefined_iff (Reverse.canonical spec) coherent (PUnit.unit, (3 : Nat)) []).mp wireUndefined

private abbrev Carry := Carrier number number pair
private def manualHeader : TwoBlock.Instruction Op number (Silmaril.coprod number number) := ⟨.header, rfl, rfl⟩
private def manualCall : TwoBlock.Instruction Op number pair := ⟨.innerRight, rfl, rfl⟩
private def manualJoin : TwoBlock.Instruction Op pair (Silmaril.coprod pair number) := ⟨.join, rfl, rfl⟩

-- Assemble the numbered graph from checked wire constructors without a source region or Loop.
private def manualBody :
    Wiring.Code (past := []) Op (Wiring.armData number number number pair) (resultData Carry)
      (.arg (runtimePort (armPorts number number number pair))) :=
  Wiring.primitive (carriedData (Silmaril.coprod (ExitCode number pair) number)) (carriedData pair)
    (.effect (.acyclic (.call (.right (X := ExitCode number pair)) manualCall))) (.arg _) (.cons (.arg (.tail .head)) .nil)
    (Wiring.primitive (carriedData pair) (resultData Carry) (.effect (.join manualJoin))
      (nextRuntime [] (carried pair)) (.cons (newest .head []) .nil)
      (Wiring.finishStep [Threaded (carried pair)]))

private def manualActivation :
    Wiring.Code (past := []) Op (carriedData Carry) (resultData Carry) (.arg (runtimePort (carried Carry))) :=
  let header := headerPorts number number pair
  Wiring.primitive (past := []) (carriedData Carry) (resultData (Route number number pair))
    (.effect (.header manualHeader)) (.arg _) (.cons (.arg .head) .nil)
    (Wiring.choice (Wiring.armData number number number pair) (resultData Carry) Wiring.exitArm manualBody
      (newest .head []) (nextRuntime [] header)
      (.cons (.arg .head) (.cons (newest (.tail .head) []) .nil))
      (Wiring.finishStep [Threaded header]))

private def manualTerm :
    Closed (Pure Ty) (Effect Op) (carriedData Carry) (carriedData Carry) [Threaded (carried Carry)] :=
  ⟨_, .theta (.arg (runtimePort (carried Carry))) (carriedData Carry) (.cons (.arg .head) .nil)
    manualActivation.1 (children := fun _ => manualActivation.2.1) (fun _ => manualActivation.2.2)
    (.ret (nextRuntime [] (carried Carry)) (.cons (newest .head []) .nil))⟩

private def manualGraph : Graph Op number number pair := manualTerm.1.toGraph

private def manualDecomposition : Reverse.Decomposition manualGraph number pair where
  checked := manualTerm.2.collect
  view := by
    exact .loop manualHeader (.call manualCall) manualJoin
  wiring := by rfl

example :
    (Reverse.raise manualDecomposition).1 =
      .cfg (.br 0 (.var 0)) 3
        (Fin.cases (.case (.op .header (.var 0)) (.br 3 (.var 0)) (.br 2 (.var 0)))
          (fun i => Fin.cases
            (.case (.op .join (.var 0)) (.br 4 (.var 0)) (.br 0 (.var 0)))
            (fun _ => .br 1 (.op .innerRight (.var 0))) i)) := by
  apply congrArg (Isotope.LambdaSSA.Region.cfg (.br 0 (.var 0)) 3)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · exact k.eq_zero ▸ rfl

end Reverse

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Tests

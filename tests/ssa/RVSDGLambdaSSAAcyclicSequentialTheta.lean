module

import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Wires.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs
import Silmaril.Raw.SSA.Isotope.Semantics.Model

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Tests

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

private inductive Op | enterFirst | bodyFirst | joinFirst | enterSecond | bodySecond | joinSecond

local instance : HasTy Op Ty :=
  ⟨(fun | .joinSecond => pair | _ => number),
   (fun
    | .enterFirst | .joinFirst | .enterSecond => .coprod number number
    | .bodyFirst => number
    | .bodySecond => pair
    | .joinSecond => .coprod pair number)⟩

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
  | .enterFirst, n => StateT.mk fun token => Part.some (.inr n, token ++ [1])
  | .bodyFirst, n => StateT.mk fun token => Part.some (n, token ++ [2])
  | .joinFirst, n => StateT.mk fun token =>
    let input : Nat := n
    Part.some (if input = 2 then .inr (1 : Nat) else if input = 0 then .inr (0 : Nat) else .inl n,
      token ++ [3])
  | .enterSecond, n => StateT.mk fun token => Part.some (.inr n, token ++ [4])
  | .bodySecond, n => StateT.mk fun token => Part.some ((n, token.length), token ++ [5])
  | .joinSecond, (n, seen) => StateT.mk fun token =>
    let input : Nat := n
    Part.some (if input = 1 then .inr (3 : Nat) else .inl (n, seen), token ++ [6])

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

private def spec : Loops Op number number number number number pair number pair :=
  ⟨⟨⟨.enterFirst, rfl, rfl⟩, .instruction ⟨.bodyFirst, rfl, rfl⟩, ⟨.joinFirst, rfl, rfl⟩⟩,
    ⟨⟨.enterSecond, rfl, rfl⟩, .instruction ⟨.bodySecond, rfl, rfl⟩, ⟨.joinSecond, rfl, rfl⟩⟩⟩

private def lowered := Wires.lower (.loops spec)
private def afterFirst : List Nat := [1,2,3,1,2,3]
private def afterSecondFeedback : List Nat := afterFirst ++ [4,5,6]
private def finalToken : List Nat := afterSecondFeedback ++ [4,5,6]
private def exit2 : LabelDen [number,pair] := .inr (.inl ((3 : Nat), (10 : Nat)))
private def middle : LabelDen [number,number] := .inr (.inl (1 : Nat))
private def first : Nat → Runtime (LabelDen [number,number] ⊕ Nat) :=
  ExplicitRuntime.round (ε := Bool) spec.first
private def second : Nat → Runtime (LabelDen [number,pair] ⊕ Nat) :=
  ExplicitRuntime.round (ε := Bool) spec.second

private theorem feedback :
    Elgot.StateT.body first (2, []) = Part.some (.inr (1, [1,2,3])) := by
  simp [Elgot.StateT.body, first, ExplicitRuntime.round, spec, ExplicitRuntime.bodyAction,
    callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def]

private theorem handoff :
    Elgot.StateT.body first (1, [1,2,3]) = Part.some (.inl (middle, afterFirst)) := by
  simp [Elgot.StateT.body, first, ExplicitRuntime.round, spec, ExplicitRuntime.bodyAction,
    callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def, middle, afterFirst]

private theorem initiallyNoExit (token : List Nat) :
    Elgot.StateT.body first (0, token) = Part.some (.inr (0, token ++ [1,2,3])) := by
  simp [Elgot.StateT.body, first, ExplicitRuntime.round, spec, ExplicitRuntime.bodyAction,
    callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def, List.append_assoc]

private theorem secondFeedback :
    Elgot.StateT.body second (1, afterFirst) = Part.some (.inr (3, afterSecondFeedback)) := by
  simp [Elgot.StateT.body, second, ExplicitRuntime.round, spec, ExplicitRuntime.bodyAction,
    callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def,
    afterFirst, afterSecondFeedback]

private theorem secondDone :
    Elgot.StateT.body second (3, afterSecondFeedback) = Part.some (.inl (exit2, finalToken)) := by
  simp [Elgot.StateT.body, second, ExplicitRuntime.round, spec, ExplicitRuntime.bodyAction,
    callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def,
    afterFirst, afterSecondFeedback, exit2, finalToken]

private theorem firstRun : (iter first 2).run [] = Part.some (middle, afterFirst) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  exact .more (by rw [feedback]; exact Part.mem_some_iff.mpr rfl)
    (.done (by rw [handoff]; exact Part.mem_some_iff.mpr rfl))

private theorem secondRun : (iter second 1).run afterFirst = Part.some (exit2, finalToken) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  exact .more (by rw [secondFeedback]; exact Part.mem_some_iff.mpr rfl)
    (.done (by rw [secondDone]; exact Part.mem_some_iff.mpr rfl))

private theorem noFirstRun (token : List Nat) : (iter first 0).run token = Part.none := by
  rw [Elgot.StateT.run_iter, Part.eq_none_iff]
  intro out existsReturn
  rw [Elgot.Part.mem_iter_iff] at existsReturn
  have noZero (input : Nat × List Nat) (output : LabelDen [number,number] × List Nat)
      (run : Elgot.Part.Runs (Elgot.StateT.body first) input output) : input.1 ≠ 0 := by
    induction run with
    | @done input output last =>
      obtain ⟨n, state⟩ := input
      intro zero
      change n = 0 at zero
      subst n
      rw [initiallyNoExit] at last
      simp at last
    | @more input next output move _ ih =>
      obtain ⟨n, state⟩ := input
      intro zero
      change n = 0 at zero
      subst n
      rw [initiallyNoExit] at move
      exact ih (congrArg Prod.fst (Sum.inr.inj (Part.mem_some_iff.mp move)))
  exact noZero _ _ existsReturn rfl

private theorem graphDone :
    Wires.observe (ε := Bool) lowered.1 (2 : Nat) [] =
      Part.some (ExplicitRuntime.exitTuple (exit2, finalToken)) := by
  change Wires.observe (ε := Bool) (Wires.graph spec) (2 : Nat) [] = _
  rw [Wires.graph_rounds, StateT.run_bind]
  change Part.map _ (((iter first 2).run []) >>= fun p =>
    (iter second (merge p.1)).run p.2) = _
  rw [firstRun, Part.bind_eq_bind, Part.bind_some]
  change Part.map _ ((iter second 1).run afterFirst) = _
  rw [secondRun]
  rfl

-- The first loop can only restart on zero. The second loop therefore
-- never receives an input, even though it would terminate if called.
private theorem graphNoHandoff :
    Wires.observe (ε := Bool) (σ := List Nat) lowered.1 (0 : Nat) [] = Part.none := by
  change Wires.observe (ε := Bool) (Wires.graph spec) (0 : Nat) [] = _
  rw [Wires.graph_rounds, StateT.run_bind]
  change Part.map _ (((iter first 0).run []) >>= fun p =>
    (iter second (merge p.1)).run p.2) = _
  rw [noFirstRun, Part.bind_eq_bind, Part.bind_none, Part.map_none]

private abbrev Coherent := RegionCoherent (τ := Ty) (Φ := Op) (ε := Bool) (m := Runtime)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) lowered.2.typing (PUnit.unit, (2 : Nat))).run [] =
      Part.some (exit2, finalToken) :=
  (lowered.2.region_returns_iff coherent (PUnit.unit, (2 : Nat)) exit2 [] finalToken).mp
    ((NestedTheta.Partial.observe_eq_some _ _ _ _).mp graphDone)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) lowered.2.typing (PUnit.unit, (0 : Nat))).run [] =
      Part.none :=
  (lowered.2.region_undefined_iff coherent (PUnit.unit, (0 : Nat)) []).mp graphNoHandoff

section Reverse

open OrderedTheta (carried carriedData resultData)
open OrderedRuntime.Structured (Threaded runtimePort nextRuntime)
open TwoBlock.TwoExit (Carrier ExitCode Route armPorts headerPorts)
open LinearChain.Wiring (newest)
open NestedTheta.ExplicitRuntime (thetaNode)

private def handBody {A B K E D : Ty}
    (head : TwoBlock.Instruction Op A (Silmaril.coprod E B))
    (body : TwoBlock.Instruction Op B K) (join : TwoBlock.Instruction Op K (Silmaril.coprod D A)) :
    ExplicitRuntime.Wiring.Code (past := []) Op (carriedData (Carrier A E D)) (resultData (Carrier A E D))
      (.arg (runtimePort (carried (Carrier A E D)))) :=
  let ports := headerPorts B E D
  let arms := ExplicitRuntime.Wiring.armData A B E D
  let guarded : ExplicitRuntime.Wiring.Code (past := []) Op arms (resultData (Carrier A E D))
      (.arg (runtimePort (armPorts A B E D))) :=
    ExplicitRuntime.Wiring.primitive (carriedData (Silmaril.coprod (ExitCode E D) B)) (carriedData K)
      (.effect (.acyclic (.call (.right (X := ExitCode E D)) body))) (.arg _)
      (.cons (.arg (.tail .head)) .nil)
      (ExplicitRuntime.Wiring.primitive (carriedData K) (resultData _) (.effect (.join join))
        (nextRuntime [] (carried K)) (.cons (newest .head []) .nil)
        (ExplicitRuntime.Wiring.finishStep [Threaded (carried K)]))
  ExplicitRuntime.Wiring.primitive (past := []) (carriedData _) (resultData (Route B E D))
    (.effect (.header head)) (.arg _) (.cons (.arg .head) .nil)
    (ExplicitRuntime.Wiring.choice arms (resultData _) ExplicitRuntime.Wiring.exitArm guarded
      (newest .head []) (nextRuntime [] ports)
      (.cons (.arg .head) (.cons (newest (.tail .head) []) .nil))
      (ExplicitRuntime.Wiring.finishStep [Threaded ports]))

private def firstHeader : TwoBlock.Instruction Op number (Silmaril.coprod number number) :=
  ⟨.enterFirst, rfl, rfl⟩
private def firstBody : TwoBlock.Instruction Op number number := ⟨.bodyFirst, rfl, rfl⟩
private def firstJoin : TwoBlock.Instruction Op number (Silmaril.coprod number number) :=
  ⟨.joinFirst, rfl, rfl⟩
private def secondHeader : TwoBlock.Instruction Op number (Silmaril.coprod number number) :=
  ⟨.enterSecond, rfl, rfl⟩
private def secondBody : TwoBlock.Instruction Op number pair := ⟨.bodySecond, rfl, rfl⟩
private def secondJoin : TwoBlock.Instruction Op pair (Silmaril.coprod pair number) :=
  ⟨.joinSecond, rfl, rfl⟩

-- Assemble both numbered θ children and the enclosing vertices directly.
-- In the malformed variant θ₂ bypasses the link's token result while
-- still reading the link's payload.
private def manualTerm (bypass : Bool) : Wires.Reverse.ClosedTerm Op number number number pair :=
  let fp := Wires.FirstPorts number number
  let sp := Wires.SecondPorts number number pair
  let beforeLink := [Threaded fp]
  let afterLink := beforeLink ++ [Threaded sp]
  let a := handBody (D := number) firstHeader firstBody firstJoin
  let b := handBody (D := pair) secondHeader secondBody secondJoin
  .bind (thetaNode (.arg (runtimePort fp)) (.cons (.arg .head) .nil) a.1)
      (fun _ => (Wires.liftChecked a.2.2).1) <|
    .bind (.ofBase (OrderedRuntime.Structured.primitiveNode (nextRuntime [] fp)
          (carriedData _) (carriedData _) (.effect .link) (.cons (newest .head []) .nil)))
        (fun i => i.elim0) <|
      .bind (thetaNode (if bypass then .output (0 : Fin 2) (.tail .head) else nextRuntime beforeLink sp)
          (.cons (newest .head beforeLink) .nil) b.1)
        (fun _ => (Wires.liftChecked b.2.2).1) <|
        .ret (OrderedRuntime.Structured.withRuntime (nextRuntime afterLink sp)
          (.cons (newest .head afterLink) .nil))

private def manualGraph (bypass : Bool) : Wires.Graph Op number number number pair :=
  (manualTerm bypass).toGraph

private def decomposition : Wires.Reverse.Decomposition (manualGraph false) number number number pair where
  checked := (Wires.code spec).2.collect
  labels := ([.header firstHeader, .gamma [[.headerExit], [.call firstBody, .join firstJoin]]],
    [.header secondHeader, .gamma [[.headerExit], [.call secondBody, .join secondJoin]]])
  shape := by rfl
  view := ⟨.loop firstHeader (.call firstBody) firstJoin, .loop secondHeader (.call secondBody) secondJoin⟩
  wiring := by rfl

private def recovered := Wires.Reverse.raise decomposition

example : recovered.1 = region spec := rfl

example : (Wires.Reverse.raise (Wires.Reverse.canonical spec)).1 = region spec :=
  Wires.Reverse.raise_canonical spec

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recovered.2.typing (PUnit.unit, (2 : Nat))).run [] =
      Part.some (exit2, finalToken) := by
  apply (Wires.Reverse.raise_returns_iff decomposition coherent (PUnit.unit, (2 : Nat)) exit2 [] finalToken).mp
  exact (NestedTheta.Partial.observe_eq_some _ _ _ _).mp graphDone

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recovered.2.typing (PUnit.unit, (0 : Nat))).run [] =
      Part.none :=
  (Wires.Reverse.raise_undefined_iff decomposition coherent (PUnit.unit, (0 : Nat)) []).mp graphNoHandoff

example (coherent : Coherent) :
    Part.map (ExplicitRuntime.exitTuple (A := number))
        ((Categorical.stateDenote (ε := Bool) (σ := List Nat) decomposition.view.decode (PUnit.unit, (2 : Nat))).run []) =
      Part.some (ExplicitRuntime.exitTuple (exit2, finalToken)) :=
  (Categorical.raised_state_observe decomposition coherent (PUnit.unit, (2 : Nat)) []).symm.trans graphDone

example (coherent : Coherent) :
    Part.map (ExplicitRuntime.exitTuple (A := number))
        ((Categorical.stateDenote (ε := Bool) (σ := List Nat) decomposition.view.decode (PUnit.unit, (0 : Nat))).run []) =
      Part.none :=
  (Categorical.raised_state_observe decomposition coherent (PUnit.unit, (0 : Nat)) []).symm.trans graphNoHandoff

-- The two graphs have the same typed labels. The full wiring certificate
-- rejects the stale token edge at the second θ.
example : Wires.Reverse.read (manualGraph true).toTerm = Wires.Reverse.read (manualGraph false).toTerm := rfl

example : ¬ Nonempty (Wires.Reverse.Decomposition (manualGraph true) number number number pair) := by
  rintro ⟨d⟩
  have edge := congrArg (fun g : Wires.Graph Op number number number pair =>
    (g.nodes (2 : Fin 3)).inputs.addresses) d.wiring
  change [Address.output 1 0, Address.output 1 1] = [Address.output 1 0, Address.output 0 1] at edge
  cases edge

end Reverse

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Tests

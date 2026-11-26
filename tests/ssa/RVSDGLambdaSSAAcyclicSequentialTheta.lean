module

import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Wires.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Atomic.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs
import Silmaril.Raw.SSA.Isotope.Semantics.Model
meta import Silmaril.SSA.Isotope.Types.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Check.Defs

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

private inductive Op | gate | enterFirst | bodyFirst | joinFirst | enterSecond | bodySecond | joinSecond
  deriving DecidableEq

local instance : HasTy Op Ty :=
  ⟨(fun | .joinSecond => pair | _ => number),
   (fun
    | .gate => TwoBlock.TwoExit.Carrier number number number
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
  | .gate, n => StateT.mk fun token =>
    if (show Nat from n) = 99 then Part.none
    else Part.some (if (show Nat from n) = 0 then .inl (.inr (1 : Nat)) else .inr n, token ++ [9])
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

namespace FlatLink

private def guarded : Conditional.Guarded Op number number number number number number :=
  ⟨⟨.gate, rfl, rfl⟩, spec.first⟩

private def linked := Flat.link (Flat.Fragment.guarded guarded) (Flat.Fragment.loop spec.second)
private def guardedToken : List Nat := [9] ++ afterFirst
private def guardedFinal : List Nat := [9] ++ finalToken
private def guardedExit : LabelDen [number,pair] := .inr (.inl ((3 : Nat), (11 : Nat)))

private theorem firstGuardedRun : (iter first 2).run [9] = Part.some (middle, guardedToken) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  refine .more (a' := (1, [9,1,2,3])) ?_ (.done ?_)
  all_goals
    simp [Elgot.StateT.body, first, ExplicitRuntime.round, spec, ExplicitRuntime.bodyAction,
      callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure, Part.bind_eq_bind,
      Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def, middle, guardedToken, afterFirst]

private theorem secondGuardedRun : (iter second 1).run guardedToken = Part.some (guardedExit, guardedFinal) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  refine .more (a' := (3, [9] ++ afterSecondFeedback)) ?_ (.done ?_)
  all_goals
    simp [Elgot.StateT.body, second, ExplicitRuntime.round, spec, ExplicitRuntime.bodyAction,
      callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure, Part.bind_eq_bind,
      Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def,
      guardedToken, guardedExit, guardedFinal, afterFirst, afterSecondFeedback, finalToken]

private theorem gateEnters :
    (Conditional.gateAction (ε := Bool) (m := Runtime) guarded (2 : Nat)).run [] =
      Part.some (.inr (2 : Nat), [9]) := by
  simp [Conditional.gateAction, guarded, callCase_run, instruction]

private theorem gateUndefined :
    (Conditional.gateAction (ε := Bool) (m := Runtime) guarded (99 : Nat)).run [] = Part.none := by
  simp [Conditional.gateAction, guarded, callCase_run, instruction]

private theorem guardedReturns :
    Conditional.returns (ε := Bool) (Conditional.graph guarded) (2 : Nat) [] middle guardedToken := by
  apply (NestedTheta.Partial.observe_eq_some _ _ _ _).mp
  change Conditional.observe (ε := Bool) (Conditional.graph guarded) (2 : Nat) [] = _
  rw [Conditional.graph_observe, StateT.run_bind, Part.bind_eq_bind, gateEnters, Part.bind_some]
  change Part.map _ ((iter first 2).run [9]) = _
  rw [firstGuardedRun]
  rfl

private theorem consumerReturns :
    ExplicitRuntime.returns (ε := Bool) (ExplicitRuntime.graph spec.second)
      (merge middle) guardedToken guardedExit guardedFinal := by
  apply (NestedTheta.Partial.observe_eq_some _ _ _ _).mp
  change ExplicitRuntime.observe (ε := Bool) (ExplicitRuntime.graph spec.second) (1 : Nat) guardedToken = _
  rw [ExplicitRuntime.graph_observe]
  change Part.map _ ((iter second 1).run guardedToken) = _
  rw [secondGuardedRun]
  rfl

-- Both loops take feedback. The consumer reads the prefix added by the gate
-- and producer, so reversing the effects or resetting the token changes the result.
example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) linked.typing (PUnit.unit, (2 : Nat))).run [] =
      Part.some (guardedExit, guardedFinal) :=
  (Flat.guarded_loop_returns_iff guarded spec.second coherent (PUnit.unit, (2 : Nat))
    guardedExit [] guardedFinal).mpr ⟨middle, guardedToken, guardedReturns, consumerReturns⟩

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) linked.typing (PUnit.unit, (99 : Nat))).run [] =
      Part.none := by
  rw [Flat.denote_link _ _ coherent, Flat.Fragment.guarded_denote, Conditional.region_gate _ coherent]
  simp only [StateT.run_bind, Part.bind_eq_bind, gateUndefined, Part.bind_none]

private noncomputable def recoveredLink :=
  Flat.recover (Conditional.Reverse.canonical guarded) (ExplicitRuntime.Reverse.canonical spec.second)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recoveredLink.typing (PUnit.unit, (2 : Nat))).run [] =
      Part.some (guardedExit, guardedFinal) :=
  (Flat.recover_returns_iff (Conditional.Reverse.canonical guarded)
    (ExplicitRuntime.Reverse.canonical spec.second) coherent (PUnit.unit, (2 : Nat))
    guardedExit [] guardedFinal).mpr ⟨middle, guardedToken, guardedReturns, consumerReturns⟩

private def numbered := Flat.Numbered.compile guarded spec.second
private noncomputable def numberedView := Flat.Numbered.canonical guarded spec.second

-- Outer vertices are the classifier, γ, carrier conversion, and relocated θ.
-- Both data and token must follow the two cut edges.
example : (numbered.nodes (2 : Fin 4)).inputs.addresses =
    [Address.output 1 0, Address.output 1 1] := rfl

example : (numbered.nodes (3 : Fin 4)).inputs.addresses =
    [Address.output 2 0, Address.output 2 1] := rfl

example : numbered.results.addresses = [Address.output 3 0, Address.output 3 1] := rfl

example : ((numbered.children (1 : Fin 4) (1 : Fin 2)).nodes (0 : Fin 1)).kind.arity = 1 := rfl

example : (numbered.nodes (3 : Fin 4)).kind.arity = 1 := rfl

example : numberedView.recover.region = linked.region :=
  congrArg Flat.Fragment.region (Flat.Numbered.recover_canonical guarded spec.second)

private theorem numberedReturns :
    Flat.Numbered.returns (ε := Bool) numbered (2 : Nat) [] guardedExit guardedFinal := by
  apply (NestedTheta.Partial.observe_eq_some _ _ _ _).mp
  change Flat.Numbered.observe (ε := Bool) numbered (2 : Nat) [] = _
  exact (Flat.Numbered.compile_after guarded spec.second (2 : Nat) [] guardedToken middle guardedReturns).trans
    ((NestedTheta.Partial.observe_eq_some _ _ _ _).mpr consumerReturns)

private theorem numberedAbsent : Flat.Numbered.observe (ε := Bool) numbered (99 : Nat) ([] : List Nat) = Part.none := by
  apply Flat.Numbered.compile_no_producer guarded spec.second
  rw [Conditional.graph_observe, StateT.run_bind, Part.bind_eq_bind, gateUndefined, Part.bind_none, Part.map_none]

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) numberedView.recover.typing (PUnit.unit, (2 : Nat))).run [] =
      Part.some (guardedExit, guardedFinal) :=
  (numberedView.region_returns_iff coherent (PUnit.unit, (2 : Nat)) guardedExit [] guardedFinal).mp numberedReturns

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) numberedView.recover.typing (PUnit.unit, (99 : Nat))).run [] =
      Part.none :=
  (numberedView.region_undefined_iff coherent (PUnit.unit, (99 : Nat)) []).mp numberedAbsent

namespace Recognition

open Flat.Numbered.Recognize
open OrderedTheta (carried results)
open OrderedRuntime.Structured (Threaded)
open TwoBlock.TwoExit (Carrier)

private def components : Components Op number number number number pair :=
  ⟨number, number, number, pair, guarded, spec.second⟩

private theorem parsed : candidate numbered = some components := rfl

private def accepted : Match numbered := ⟨components, rfl⟩

example : recognize numbered = some accepted :=
  complete components parsed rfl

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) accepted.recover.typing (PUnit.unit, (2 : Nat))).run [] =
      Part.some (guardedExit, guardedFinal) :=
  (accepted.region_returns_iff coherent (PUnit.unit, (2 : Nat)) guardedExit [] guardedFinal).mp numberedReturns

private abbrev one := Body.instruction firstBody

private def nestedChoice : Body Op number number :=
  .choice firstHeader one (.choice firstHeader (.sequence one one) one)

private def compoundProducer : Conditional.Guarded Op number number number number number number :=
  { guarded with loop := { guarded.loop with body := .sequence nestedChoice (.sequence one one) } }

private def compoundConsumer : Loop Op number number pair number pair :=
  { spec.second with body := .sequence one (.instruction secondBody) }

private def compound := Flat.Numbered.compile compoundProducer compoundConsumer

private theorem producerForm : RightAssociated compoundProducer.loop.body :=
  .thenChoice firstHeader (.instruction firstBody)
    (.choice firstHeader (.thenInstruction firstBody (.instruction firstBody)) (.instruction firstBody))
    (.thenInstruction firstBody (.instruction firstBody))

private theorem consumerForm : RightAssociated compoundConsumer.body :=
  .thenInstruction firstBody (.instruction secondBody)

private def compoundMatch : Match compound :=
  ⟨⟨number, number, number, pair, compoundProducer, compoundConsumer⟩, rfl⟩

example : recognize compound = some compoundMatch :=
  recognize_rightAssociated _ _ producerForm consumerForm

example : compoundMatch.recover = Flat.Numbered.Source compoundProducer compoundConsumer := rfl

private def leftAssociatedProducer : Conditional.Guarded Op number number number number number number :=
  { guarded with loop := { guarded.loop with body := .sequence (.sequence nestedChoice one) one } }

private def regrouped := Flat.Numbered.compile leftAssociatedProducer compoundConsumer

example : (recognize regrouped).isSome = true :=
  complete_generated leftAssociatedProducer compoundConsumer

-- The original association is immaterial to the numbered graph.
example : regrouped = compound := rfl

-- An analysis client can start from the accepted graph and its wire certificate.
example : Nonempty (NestedTheta.ExplicitRuntime.EntryChecked (a := OrderedTheta.carriedData number)
    (b := OrderedTheta.carriedData (Wires.Second number number pair)) compound.toTerm) :=
  ⟨compoundMatch.checked⟩

private abbrev InputPorts := Threaded (carried number)
private abbrev ProducerPorts := Conditional.Signatures number number number
private abbrev JointTerm := NestedTheta.Term (Wires.Op Op) InputPorts []
  (Flat.Numbered.JoinedSignatures number number number pair)
  (Threaded (Flat.Numbered.Stop number number pair))

private def useStaleCarrier {ty : OrderedRuntime.Structured.Ty Ty}
    (source : Origin InputPorts ProducerPorts ty) : Origin InputPorts ProducerPorts ty :=
  if h : PortType.value (Carrier number number number) = ty then
    Eq.mp (congrArg (Origin InputPorts ProducerPorts) h) (.output (0 : Fin 2) (.tail .head))
  else source

-- The stale carrier has the same type and retains the same live token
-- input. Its data comes from the classifier instead of the selected γ.
private def staleHandoff : Flat.Numbered.Graph Op number number number number pair :=
  let term : JointTerm := match numbered.toTerm with
    | .bind gate gateKids (.bind gamma arms (.bind link linkKids tail)) =>
      let inputs := link.inputs.map (fun _ source => useStaleCarrier source)
      .bind gate gateKids (.bind gamma arms (.bind { link with inputs } linkKids tail))
  term.toGraph

example : (staleHandoff.nodes (2 : Fin 4)).inputs.addresses =
    [Address.output 0 1, Address.output 1 1] := rfl

example : cut staleHandoff = none := rfl

example : recognize staleHandoff = none := reject_cut rfl

private def useStaleToken {past : List (Ports (OrderedRuntime.Structured.Ty Ty))}
    {ty : OrderedRuntime.Structured.Ty Ty} (source : Origin InputPorts past ty) : Origin InputPorts past ty :=
  if h : OrderedRuntime.Structured.runtime = ty then
    Eq.mp (congrArg (Origin InputPorts past) h) (.arg (.tail .head))
  else source

-- The cut itself is unchanged here. The final comparison must inspect
-- addresses inside the producer, beyond the handoff guard.
private def staleGamma : Flat.Numbered.Graph Op number number number number pair :=
  let term : JointTerm := match numbered.toTerm with
    | .bind gate gateKids (.bind gamma arms tail) =>
      let inputs := gamma.inputs.map (fun _ source => useStaleToken source)
      .bind gate gateKids (.bind { gamma with inputs } arms tail)
  term.toGraph

example : components.graph ≠ staleGamma := by
  intro equal
  have wire := congrArg (fun g : Flat.Numbered.Graph Op number number number number pair =>
    (g.nodes (1 : Fin 4)).inputs.addresses) equal
  change [Address.output 0 0, Address.output 0 1, Address.output 0 2] =
    [Address.output 0 0, Address.output 0 1, Address.arg 1] at wire
  cases wire

#eval show IO Unit from do
  unless (recognize numbered).isSome do
    throw (IO.userError "recognizer rejected the two-loop numbered graph")
  unless (recognize regrouped).isSome do
    throw (IO.userError "recognizer rejected the nested γ and sequence bodies")
  unless (recognize staleHandoff).isNone do
    throw (IO.userError "recognizer accepted the stale producer data edge")
  unless (candidate staleGamma).isSome do
    throw (IO.userError "the nested wiring check was not exercised")
  unless (recognize staleGamma).isNone do
    throw (IO.userError "recognizer ignored the stale gamma token edge")

end Recognition

end FlatLink

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Tests

module

import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Thms
meta import Silmaril.SSA.Isotope.Types.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Defs

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Regression

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open TwoBlock.TwoExit (Carrier callCase)
open Silmaril.Elgot (iter)
open Sequential
open Sequential.Flat.Serial (returns observe)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private abbrev Ty := Silmaril.Ty Unit
private abbrev number : Ty := .base ()
private def Value : Ty → Type
  | .base _ => Nat
  | .product a b => Value a × Value b
  | .unit => PUnit
  | .coprod a b => Value a ⊕ Value b
  | .empty => PEmpty
private abbrev Runtime := StateT Nat Part

private inductive Op
  | gate (pivot stamp : Nat)
  | header (stamp : Nat)
  | body
  | join
  deriving DecidableEq

local instance : HasTy Op Ty :=
  ⟨fun _ => number, fun
    | .gate .. => Carrier number number number
    | .header _ | .join => .coprod number number
    | .body => number⟩

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
  | .gate pivot stamp, n => StateT.mk fun token =>
    Part.some (if (show Nat from n) < pivot then .inl (.inr n) else .inr n, 10 * token + stamp)
  | .header stamp, n => StateT.mk fun token =>
    if stamp = 6 ∧ (show Nat from n) = 99 then Part.none
    else
      Part.some (if stamp = 3 ∧ (show Nat from n) = 0 then .inr n
        else .inl (if stamp = 8 then token else n), 10 * token + stamp)
  | .body, n => pure n
  | .join, n => pure (.inr ((show Nat from n) + 1))

local instance : InstructionModel Op Ty Bool Runtime where
  denote := instruction
  denotePure _ h := False.elim (by change true = false at h; cases h)
  denote_pure _ h _ := False.elim (by change true = false at h; cases h)

private def op (f : Op) : TwoBlock.Instruction Op (instrSrc (τ := Ty) f) (instrTrg (τ := Ty) f) :=
  ⟨f, rfl, rfl⟩

private abbrev Exits := LabelDen [number, number]

private theorem call_run {X Y : Ty} (p : TwoBlock.Instruction Op X Y) (input : Value X) :
    TwoBlock.call (ε := Bool) (m := Runtime) p input =
      p.output ▸ instruction p.op (p.input.symm ▸ input) := by
  obtain ⟨op, src, dst⟩ := p
  subst X
  subst Y
  unfold TwoBlock.call
  change instruction op input >>= pure = instruction op input
  exact bind_pure _

private theorem case_run {X L R : Ty} (p : TwoBlock.Instruction Op X (Silmaril.coprod L R))
    (input : Value X) :
    callCase (ε := Bool) (m := Runtime) p input =
      (show Runtime (Value (Silmaril.coprod L R)) from p.output ▸ instruction p.op (p.input.symm ▸ input)) := by
  unfold callCase
  rw [call_run]
  change (_ : Runtime (Value L ⊕ Value R)) >>= pure = _
  exact bind_pure _

private def stage (stamp : Nat) : Loop Op number number number number number :=
  ⟨op (.header stamp), .instruction (op .body), op .join⟩

private def gate (pivot stamp : Nat) : TwoBlock.Instruction Op number (ChoiceCarrier number number) :=
  ⟨.gate pivot stamp, rfl, rfl⟩

private def inner :=
  Syntax.branch (X := number) (Z := number) (gate 1 2)
    (.loop (stage 3)) (.loop (stage 4)) (.loop (stage 5))

private def exampleCFG :=
  Syntax.branch (X := number) (Z := number) (gate 3 1) inner
    (.loop (stage 6)) (.link (.loop (stage 7)) (.loop (stage 8)))

private def lowered := lower exampleCFG
private abbrev Coherent := RegionCoherent (τ := Ty) (Φ := Op) (ε := Bool) (m := Runtime)
private abbrev step (digit : Nat) := ExplicitRuntime.round (ε := Bool) (m := Runtime) (stage digit)

private theorem round_run (digit n token : Nat) : Elgot.StateT.body (step digit) (n, token) =
    if digit = 6 ∧ n = 99 then Part.none
    else if digit = 3 ∧ n = 0 then Part.some (.inr (n + 1, 10 * token + digit))
    else Part.some (.inl ((.inl (if digit = 8 then token else n) : Exits), 10 * token + digit)) := by
  by_cases bad : digit = 6 ∧ n = 99
  · simp [Elgot.StateT.body, step, ExplicitRuntime.round, stage, case_run, op, instruction, bad]
  · by_cases again : digit = 3 ∧ n = 0 <;>
      simp [Elgot.StateT.body, step, ExplicitRuntime.round, stage, ExplicitRuntime.bodyAction, op,
        case_run, call_run, instruction, bad, again, Elgot.StateT.distribute, Function.comp_def]

private noncomputable abbrev runStage (digit : Nat) (n : TyDen number) := iter (step digit) n

private theorem stage_returns (digit n token : Nat) (defined : ¬(digit = 6 ∧ n = 99))
    (ends : ¬(digit = 3 ∧ n = 0)) :
    (runStage digit n).run token =
      Part.some ((.inl (if digit = 8 then token else n) : Exits), 10 * token + digit) := by
  rw [runStage, Part.eq_some_iff, Elgot.StateT.run_iter, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.done
  simp [round_run, defined, ends]

private theorem feedback_returns :
    (runStage 3 (0 : Nat)).run 12 = Part.some ((.inl (1 : Nat) : Exits), 1233) := by
  rw [runStage, Part.eq_some_iff, Elgot.StateT.run_iter, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.more (a' := ((1 : Nat), 123))
  · have h : Elgot.StateT.body (step 3) ((0 : Nat), 12) = Part.some (.inr ((1 : Nat), 123)) :=
      round_run 3 0 12
    rw [h]
    exact Part.mem_some _
  · apply Elgot.Part.Runs.done
    have h : Elgot.StateT.body (step 3) ((1 : Nat), 123) = Part.some (.inl ((.inl (1 : Nat) : Exits), 1233)) :=
      round_run 3 1 123
    rw [h]
    exact Part.mem_some _

private theorem blocked (token : Nat) : (runStage 6 (99 : Nat)).run token = Part.none := by
  rw [runStage, Part.eq_none_iff]
  intro out h
  rw [Elgot.StateT.run_iter, Elgot.Part.mem_iter_iff] at h
  cases h with
  | done h | more h _ => rw [round_run] at h; exact Part.notMem_none _ h

private def route (pivot stamp : Nat) (l r : TyDen number → Runtime Exits) (n : TyDen number) : Runtime Exits :=
  StateT.mk fun token =>
    (if (show Nat from n) < pivot then l n else r n).run (10 * token + stamp)

private theorem gate_runs (pivot stamp : Nat) (n : TyDen number) (l r : TyDen number → Runtime Exits) :
    (callCase (ε := Bool) (m := Runtime) (gate pivot stamp) n >>= fun
      | .inl x => l (Sum.elim id id (TypeModel.coprodEquiv number number x))
      | .inr y => r y) = route pivot stamp l r n := by
  funext token
  change (StateT.run (_ >>= _) token) = _
  rw [StateT.run_bind, case_run, Part.bind_eq_bind]
  change (Part.some ((if (show Nat from n) < pivot then .inl (.inr n) else .inr n :
    (Nat ⊕ Nat) ⊕ Nat), 10 * token + stamp)).bind _ = _
  rw [Part.bind_some]
  by_cases choice : (show Nat from n) < pivot
  · simp only [route, StateT.run, choice, ite_true]
    rfl
  · simp only [route, StateT.run, choice, ite_false]
    rfl

private theorem route_left (pivot stamp n token : Nat) (l r : Nat → Runtime Exits) (selected : n < pivot) :
    (route pivot stamp l r n).run token = (l n).run (10 * token + stamp) := by
  simp [route, selected]

private theorem route_right (pivot stamp n token : Nat) (l r : Nat → Runtime Exits)
    (selected : ¬n < pivot) :
    (route pivot stamp l r n).run token = (r n).run (10 * token + stamp) := by
  simp [route, selected]

private theorem source_run (coherent : Coherent) (n : TyDen number) :
    Region.denote (ε := Bool) (m := Runtime) lowered.2.typing (PUnit.unit, n) =
      route 3 1 (fun x => route 1 2 (runStage 3) (runStage 4) x >>= fun e => runStage 5 (merge e))
        (runStage 6) n >>= fun e => runStage 7 (merge e) >>= fun next => runStage 8 (merge next) := by
  change Region.denote (ε := Bool) (m := Runtime) exampleCFG.source.typing (PUnit.unit, n) = _
  simp only [exampleCFG, inner, Syntax.source, Flat.denote_link _ _ coherent, Flat.denote_fork _ _ _ coherent,
    Flat.Fragment.loop_denote, ExplicitRuntime.denote_rounds _ coherent, runStage]
  simp only [← gate_runs, step]
  simp only [runStage, step, bind_assoc]
  congr 1
  funext outer
  cases outer with
  | inr y => rfl
  | inl x =>
    dsimp only
    simp only [bind_assoc]
    congr 1
    funext selected
    cases selected <;> rfl

private def exit (n : Nat) : Exits := .inl n

-- The inner loop runs twice; both joins and the serial tail consume the accumulated token.
private theorem leftReturns (coherent : Coherent) : returns (ε := Bool) lowered.1 (0 : Nat) 0 (exit 123357) 1233578 := by
  apply (lowered.2.region_returns_iff coherent (PUnit.unit, (0 : Nat)) (exit 123357) 0 1233578).mpr
  rw [source_run coherent]
  rw [StateT.run_bind, Part.bind_eq_bind, route_left 3 1 0 0 _ _ (by decide)]
  rw [StateT.run_bind, Part.bind_eq_bind, route_left 1 2 0 _ _ _ (by decide)]
  rw [feedback_returns, Part.bind_some, stage_returns 5 _ _ (by decide) (by decide), Part.bind_some]
  change ((runStage 7 (1 : Nat) >>= fun result => runStage 8 (merge result)).run 12335) = _
  rw [StateT.run_bind, Part.bind_eq_bind, stage_returns 7 _ _ (by decide) (by decide), Part.bind_some]
  change (runStage 8 (1 : Nat)).run 123357 = _
  exact stage_returns 8 1 123357 (by decide) (by decide)

-- The outer right arm skips all of the inner diamond's actions.
private theorem rightReturns (coherent : Coherent) : returns (ε := Bool) lowered.1 (3 : Nat) 0 (exit 167) 1678 := by
  apply (lowered.2.region_returns_iff coherent (PUnit.unit, (3 : Nat)) (exit 167) 0 1678).mpr
  rw [source_run coherent]
  rw [StateT.run_bind, Part.bind_eq_bind, route_right 3 1 3 0 _ _ (by decide)]
  rw [stage_returns 6 _ _ (by decide) (by decide), Part.bind_some]
  change ((runStage 7 (3 : Nat) >>= fun result => runStage 8 (merge result)).run 16) = _
  rw [StateT.run_bind, Part.bind_eq_bind, stage_returns 7 _ _ (by decide) (by decide), Part.bind_some]
  change (runStage 8 (3 : Nat)).run 167 = _
  exact stage_returns 8 3 167 (by decide) (by decide)

private theorem noReturn (coherent : Coherent) : observe (ε := Bool) lowered.1 (99 : Nat) 0 = Part.none := by
  apply (lowered.2.region_undefined_iff coherent (PUnit.unit, (99 : Nat)) 0).mpr
  rw [source_run coherent]
  rw [StateT.run_bind, Part.bind_eq_bind, route_right 3 1 99 0 _ _ (by decide)]
  rw [blocked, Part.bind_none]

open Reverse (Normal Supported)
open OrderedRuntime.Structured (runtime)

private def normalInner :=
  Normal.branch (X := number) (Z := number) (gate 1 2)
    (.loop (stage 3)) (.loop (stage 4)) (.loop (stage 5))

private def normal :=
  Normal.branch (X := number) (Z := number) (gate 3 1) normalInner
    (.loop (stage 6)) (.link (stage 7) (.loop (stage 8)))

private theorem supported : Supported normal :=
  ⟨⟨.instruction _, .instruction _, .instruction _⟩, .instruction _, .instruction _, .instruction _⟩

private theorem recovers : Reverse.recover lowered.1 =
    some ⟨exampleCFG.source.region, .generated exampleCFG⟩ :=
  Reverse.recover_generated normal supported

private def recovered : Reverse.Fibre lowered.1 :=
  (Reverse.recover lowered.1).get (by rw [recovers]; rfl)

private theorem accepted : Reverse.recover lowered.1 = some recovered := by
  simp [recovered, recovers]

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recovered.2.typing (PUnit.unit, (0 : Nat))).run 0 =
      Part.some (exit 123357, 1233578) :=
  (Reverse.recover_returns_iff accepted coherent (PUnit.unit, (0 : Nat)) (exit 123357) 0 1233578).mp
    (leftReturns coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recovered.2.typing (PUnit.unit, (3 : Nat))).run 0 =
      Part.some (exit 167, 1678) :=
  (Reverse.recover_returns_iff accepted coherent (PUnit.unit, (3 : Nat)) (exit 167) 0 1678).mp
    (rightReturns coherent)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recovered.2.typing (PUnit.unit, (99 : Nat))).run 0 = Part.none :=
  (Reverse.recover_undefined_iff accepted coherent (PUnit.unit, (99 : Nat)) 0).mp (noReturn coherent)

private abbrev Boundary := Flat.Serial.WirePorts number number number
private abbrev FixtureSigs := Selection number number number number ++
  Flat.Serial.Joined number number number [Boundary] [Boundary]
private abbrev Graph := Flat.Serial.Graph Op number number number number number number FixtureSigs

private def staleToken {past : List (Ports (OrderedRuntime.Structured.Ty Ty))}
    {t : OrderedRuntime.Structured.Ty Ty} (wire : Origin Boundary past t) : Origin Boundary past t :=
  if same : runtime = t then Eq.mp (congrArg (Origin Boundary past) same) (.arg (.tail .head))
  else wire

-- The first loop of the shared tail still receives the γ payload.
-- Its token instead reads the type-correct original graph argument.
private def stale : Graph :=
  let term : NestedTheta.Term (Wires.Op Op) Boundary [] FixtureSigs Boundary := match lowered.1.toTerm with
    | .bind gate gateChildren (.bind fork arms (.bind next body rest)) =>
      let inputs := next.inputs.map (fun _ wire => staleToken wire)
      .bind gate gateChildren (.bind fork arms (.bind {next with inputs} body rest))
  term.toGraph

private theorem sameLabels : Reverse.scan stale.toTerm = Reverse.scan lowered.1.toTerm := by
  unfold stale
  rw [NestedTheta.Term.toTerm_toGraph]
  generalize lowered.1.toTerm = term
  cases term with
  | bind gate gateChildren rest =>
    cases rest with
    | bind fork arms rest =>
      cases rest with
      | bind next body rest =>
        cases next
        rfl

private theorem staleParses : Reverse.candidate stale = some normal := by
  unfold Reverse.candidate
  rw [sameLabels]
  exact Reverse.candidate_generated normal supported

private theorem staleDifferent : normal.toSyntax.graph ≠ stale := by
  intro eq
  have edges := congrArg (fun g : Graph =>
    match g with | .region nodes _ _ => (nodes (2 : Fin 5)).inputs.addresses) eq
  change [Address.output 1 0, Address.output 1 1] = [Address.output 1 0, Address.arg 1] at edges
  cases edges

example : Reverse.recognize stale = none :=
  Reverse.reject_wiring normal staleParses staleDifferent

-- Three loops emitted with left association have the same numbered wiring
-- as the recognizer's right-associated view in this fixture.
private def leftSerial :=
  Syntax.link (.link (.loop (stage 5)) (.loop (stage 7))) (.loop (stage 8))

private def rightSerial := Normal.link (stage 5) (.link (stage 7) (.loop (stage 8)))

example : Reverse.candidate leftSerial.graph = some rightSerial :=
  Reverse.candidate_generated rightSerial ⟨.instruction _, .instruction _, .instruction _⟩

#eval show IO Unit from do
  unless (Reverse.recover lowered.1).isSome do
    throw (IO.userError "could not recover the nested diamond and its serial tail")
  unless (Reverse.recognize leftSerial.graph).isSome do
    throw (IO.userError "could not recover the right-associated serial view")
  unless (Reverse.candidate stale).isSome && (Reverse.recognize stale).isNone do
    throw (IO.userError "structured recovery failed to certify the stale token")

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Regression

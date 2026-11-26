module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Thms

/-! A primitive produces a shaped pair and increments the state. Another
primitive of empty result type can fault, so initiality needs its value guard. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.Morphism.SSAIter (envOfBound)

namespace LambdaSSAUBShapeRegression

private inductive Op where
  | pack
  | fail

private abbrev pairTy : Ty Unit := .product (.base ()) .unit
private abbrev labels : List (Ty Unit) := [pairTy]
private abbrev payload : Value Bool := .pair (.atom true) .unit

local instance : HasTy Op (Ty Unit) where
  src _ := .unit
  trg
    | .pack => pairTy
    | .fail => .empty

private abbrev fixture : Shape.Model Op ([] : List (Ty Unit)) where
  raw := {
    α := Bool
    σ := Nat
    instr := fun op a s b t => match op with
      | .pack => a = .unit ∧ b = payload ∧ t = s + 1
      | .fail => False
    faults := fun op a s t => op = .fail ∧ a = .unit ∧ t = s + 1
    prim := fun _ _ _ => False
    bound := Fin.elim0 }
  atomType a _ := a = true
  boundTyped i := Fin.elim0 i
  instrTyped := by
    intro op a s b t _ step
    cases op with
    | pack =>
      obtain ⟨_, rfl, _⟩ := step
      exact .pair (.atom rfl) .unit
    | fail => exact step.elim

private def entry : LambdaSSA.UB.Typed (Φ := Op) [] (labels ++ labels) :=
  ⟨.br 0 (.op .pack .unit), .br (ℓ := 0) rfl (.op (f := Op.pack) .unit)⟩

private def blocks (i : Fin labels.length) :
    LambdaSSA.UB.Typed (Φ := Op) [labels.get i] (labels ++ labels) :=
  ⟨.br 1 (.var 0), .br rfl (.var (i := 0) (Fin.eq_zero i ▸ rfl))⟩

private noncomputable def packed : Region Op [] labels :=
  .feedback (R := labels) (.native entry) (fun i => .native (blocks i))

private theorem packed_returns :
    (Shape.denote packed fixture 0).Ordinary (.ret (0 : Fin 1) payload 1) := by
  unfold packed Shape.denote
  rw [denote_native_feedback entry blocks]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  exact LambdaSSA.Semantics.Region.Eval.cfg (.br (.op .unit ⟨rfl, rfl, rfl⟩))
    (.step (by decide) (.br .var) (.exit (by decide)))

private theorem etaStep :
    LambdaSSA.Region.ProductEta.Step labels
      (.let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0))) : LambdaSSA.Region Op)
      (.br 0 (.var 0)) labels :=
  .let₂Eta (i := 0) (ℓ := 0) rfl rfl

private theorem payload_typed : Shape.ValueTyped fixture.atomType payload pairTy :=
  Shape.returns_typed packed fixture 0 packed_returns

private abbrev withPayload := fixture.extend payload_typed

private theorem product_eta_returns :
    (Shape.denote (.native ⟨_, etaStep.typed.1⟩) withPayload (1 : Nat)).Ordinary
      (.ret (0 : Fin 1) payload (1 : Nat)) := by
  rw [Shape.product_eta etaStep withPayload]
  exact ⟨WithTop.coe_ne_top, LambdaSSA.Semantics.Region.Eval.br .var⟩

private theorem no_empty_input : ¬ Nonempty (Shape.Model Op ([.empty] : List (Ty Unit))) :=
  fun ⟨M⟩ => Shape.no_model_of_empty_branchValue (.var (Φ := Op) (i := 0) rfl) M

private def effectfulEmpty : LambdaSSA.UB.Typed (Φ := Op) [] [Ty.unit (α := Unit)] :=
  ⟨.let₁ (.op .fail .unit) (.br 0 .unit),
    .let₁ (.op (f := Op.fail) .unit) (.br (ℓ := 0) rfl .unit)⟩

private def immediate : LambdaSSA.UB.Typed (Φ := Op) [] [Ty.unit (α := Unit)] :=
  ⟨.br 0 .unit, .br (ℓ := 0) rfl .unit⟩

/-- A term of empty type that can fault does not justify the initiality equation. -/
private theorem empty_term_guard_needed :
    Shape.denote (.native effectfulEmpty) fixture 0 ≠ Shape.denote (.native immediate) fixture 0 := by
  intro equal
  have fault : (Shape.denote (.native effectfulEmpty) fixture 0).Ordinary (.fault 1) :=
    ⟨WithTop.coe_ne_top, LambdaSSA.Semantics.Region.Fault.let₁_arg (.op_fault .unit ⟨rfl, rfl, rfl⟩)⟩
  rw [equal] at fault
  have impossible : LambdaSSA.Semantics.Region.Fault fixture.raw.instr fixture.raw.faults
      (envOfBound fixture.raw.bound) immediate.val 0 1 := fault.2
  cases impossible with
  | br no => cases no

#print axioms Shape.term_eval_typed
#print axioms Shape.region_eval_typed
#print axioms Shape.returns_typed
#print axioms Shape.product_eta
#print axioms Shape.initial
#print axioms product_eta_returns
#print axioms no_empty_input
#print axioms empty_term_guard_needed

end LambdaSSAUBShapeRegression

module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Thms

/-! The literal postcontinuation runs after an outward exit. The dispatcher
can replay either duplicate label or take the exit. The postcontinuation can
return, fault, or diverge in a primitive. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.Codiagonal
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.Morphism.SSAIter (envOfBound)

namespace LambdaSSAUBPaperRegression

private inductive Op where
  | choose
  | mark

private abbrev τ := Ty Empty
private abbrev U : τ := .unit
private abbrev Choice : τ := .coprod U (.coprod U U)
private abbrev RawRegion := LambdaSSA.Region Op

local instance : HasTy Op τ where
  src _ := U
  trg
    | .choose => Choice
    | .mark => U

private abbrev fixture : Shape.Model Op ([] : List τ) where
  raw := {
    α := Unit
    σ := Nat
    instr := fun op a s v t => match op with
      | .choose => a = .unit ∧ (v = .inl .unit ∨ v = .inr (.inl .unit) ∨ v = .inr (.inr .unit)) ∧ t = s + 1
      | .mark => a = .unit ∧ v = .unit ∧ t = s + 10
    faults := fun op a s t => op = .mark ∧ a = .unit ∧ t = s + 11
    prim := fun op a _ => op = .mark ∧ a = .unit
    bound := Fin.elim0 }
  atomType := fun _ _ => False
  boundTyped i := Fin.elim0 i
  instrTyped := by
    intro op a s v t _ step
    cases op with
    | choose =>
      rcases step with ⟨_, rfl | rfl | rfl, _⟩
      · exact .inl .unit
      · exact .inr (.inl .unit)
      · exact .inr (.inr .unit)
    | mark =>
      obtain ⟨_, rfl, _⟩ := step
      exact .unit

private abbrev entry : RawRegion := .br 0 .unit
private abbrev body : RawRegion :=
  .let₁ (.op .choose .unit)
    (.case (.var 0) (.br 0 .unit) (.case (.var 0) (.br 1 .unit) (.br 2 .unit)))
private abbrev post : Nat → RawRegion := fun _ => .let₁ (.op .mark .unit) (.br 0 .unit)

private theorem entryTyped : ValueBranches ([] : List τ) entry [U, U] := .br (ℓ := 0) rfl .unit

private theorem bodyTyped : ValueBranches [U] body [U, U, U] :=
  .let₁ (.op (f := Op.choose) .unit)
    (.case (.var (i := 0) rfl) (.br (ℓ := 0) rfl .unit)
      (.case (.var (i := 0) rfl) (.br (ℓ := 1) rfl .unit) (.br (ℓ := 2) rfl .unit)))

private theorem postTyped : LambdaSSA.Region.LSubst.HasType ([] : List τ) [U] [U] post := by
  intro i A hi
  exact .let₁ (.op (f := Op.mark) .unit) (.br (ℓ := 0) rfl .unit)

private abbrev staged : LambdaSSA.UB.Typed (Φ := Op) [] [U] :=
  ⟨(nested entry body).lsubst post, (nested_typed entryTyped.hasType bodyTyped.hasType).lsubst postTyped⟩

private abbrev fused : LambdaSSA.UB.Typed (Φ := Op) [] [U] :=
  ⟨(flattened entry body).lsubst post, (flattened_typed entryTyped.hasType bodyTyped.hasType).lsubst postTyped⟩

private theorem same :
    Shape.denote (.native staged) fixture 0 = Shape.denote (.native fused) fixture 0 :=
  Shape.Paper.collapsePost entryTyped bodyTyped postTyped fixture 0

private abbrev fusedBlock : RawRegion :=
  .let₁ (.op .choose .unit)
    (.case (.var 0) (.br 0 .unit)
      (.case (.var 0) (.br 0 .unit) (.let₁ (.op .mark .unit) (.br 1 .unit))))

private theorem fused_syntax : fused.val = .cfg entry 1 (fun _ => fusedBlock) := rfl

private abbrev captured : Env Unit := envOfBound fixture.raw.bound
private abbrev localEnv : Env Unit := extend captured .unit

private theorem exit_choice (s : Nat) :
    Tm.Eval fixture.raw.instr localEnv (.op Op.choose .unit) s (.inr (.inr .unit)) (s + 1) :=
  .op .unit ⟨rfl, .inr (.inr rfl), rfl⟩

private theorem return_after_post :
    (Shape.denote (.native staged) fixture 0).Ordinary (.ret (0 : Fin 1) .unit 11) := by
  rw [same]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change Region.Eval fixture.raw.instr captured fused.val 0 0 .unit 11
  rw [fused_syntax]
  exact .cfg (.br .unit) (.step (by decide) (.let₁ (exit_choice 0)
    (.case_inr .var (.case_inr .var (.let₁ (.op .unit ⟨rfl, rfl, rfl⟩) (.br .unit))))) (.exit (by decide)))

private theorem fault_after_post : (Shape.denote (.native staged) fixture 0).Ordinary (.fault 12) := by
  rw [same]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change Region.Fault fixture.raw.instr fixture.raw.faults captured fused.val 0 12
  rw [fused_syntax]
  exact .cfg_follow (.br .unit) (.body (by decide)
    (.let₁_body (exit_choice 0) (.case_inr .var (.case_inr .var (.let₁_arg (.op_fault .unit ⟨rfl, rfl, rfl⟩))))))

private theorem primitive_div_after_post : (Shape.denote (.native staged) fixture 0).Ordinary .diverge := by
  rw [same]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change External.Diverges fixture.raw.instr fixture.raw.prim (.region captured fused.val 0)
  rw [fused_syntax]
  apply External.Diverges.fold_core
  apply DivergenceStep.cfg_follow (Region.Eval.br Tm.Eval.unit)
  apply External.Diverges.fold_core
  refine .follow_body (by decide) ?_
  apply External.Diverges.fold_core
  apply DivergenceStep.let₁ (exit_choice 0)
  apply External.Diverges.fold_core
  apply DivergenceStep.case_inr Tm.Eval.var
  apply External.Diverges.fold_core
  apply DivergenceStep.case_inr Tm.Eval.var
  exact .fold (.let₁_arg (.primitive .unit ⟨rfl, rfl⟩))

private theorem replay_step (outer : Bool) (s : Nat) :
    Region.Eval fixture.raw.instr localEnv fusedBlock s 0 .unit (s + 1) := by
  cases outer with
  | false => exact .let₁ (.op .unit ⟨rfl, .inl rfl, rfl⟩) (.case_inl .var (.br .unit))
  | true => exact .let₁ (.op .unit ⟨rfl, .inr (.inl rfl), rfl⟩) (.case_inr .var (.case_inl .var (.br .unit)))

private theorem internal_div (outer : Bool) : (Shape.denote (.native staged) fixture 0).Ordinary .diverge := by
  rw [same]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change External.Diverges fixture.raw.instr fixture.raw.prim (.region captured fused.val 0)
  rw [fused_syntax]
  apply External.Diverges.of_internal
  apply Diverges.fold
  apply DivergenceStep.cfg_follow (Region.Eval.br Tm.Eval.unit)
  refine Diverges.coinduct (fun c =>
    ∃ s : Nat, c = .follow captured (fun _ : Fin 1 => fusedBlock) 0 .unit s) ?_ ⟨0, rfl⟩
  rintro _ ⟨s, rfl⟩
  exact .follow_next (by decide) (replay_step outer s) ⟨s + 1, rfl⟩

#print axioms Shape.Paper.collapse_obs
#print axioms Shape.Paper.collapsePost
#print axioms Shape.Paper.uniform_square_right
#print axioms Shape.Paper.uniform_square_left_branch
#print axioms return_after_post
#print axioms fault_after_post
#print axioms primitive_div_after_post
#print axioms internal_div

end LambdaSSAUBPaperRegression

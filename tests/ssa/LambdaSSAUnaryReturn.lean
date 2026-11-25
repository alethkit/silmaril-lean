module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.InstructionFree.Thms

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation

/-! The unary return projects and flips a tag. The two guarded step
representatives recur on the left tag and exit on the right tag. -/

namespace UnaryStateChange

local instance : HasTy Empty (Ty Unit) := ⟨Empty.elim, Empty.elim⟩

private abbrev Types := Ty Unit
private def out : Types := .unit
private def bit : Types := .coprod .unit .unit
private def state : Types := .product .unit bit

private def flip : Tm Empty := .case (.var 0) (.inr (.var 0)) (.inl (.var 0))
private def changeState : Tm Empty := .let₁ (.let₂ (.var 0) (.var 0)) flip
private def initialValue : Tm Empty := .pair .unit (.inr .unit)
private def nextValue : Tm Empty := .pair .unit (.inl .unit)
private def nextState : Tm Empty := .let₁ (.let₂ nextValue (.var 0)) flip
private def entry : Region Empty := .br 0 initialValue
private def sourceStep : Region Empty :=
  .let₁ changeState (.case (.var 0) (.br 0 nextValue) (.br 1 .unit))
private def targetStep : Region Empty :=
  .case (.var 0) (.let₁ nextState (.br 0 (.var 0))) (.br 1 .unit)

private theorem flip_typed (Γ : VCtx Types) : Tm.HasType (bit :: Γ) flip bit :=
  .case (.var (i := 0) rfl) (.inr (.var (i := 0) rfl)) (.inl (.var (i := 0) rfl))

private theorem ht : Tm.HasType [state] changeState bit :=
  .let₁ (.let₂ (.var (i := 0) rfl) (.var (i := 0) rfl)) (flip_typed _)

private theorem free : InstructionFree changeState := by
  let : HasEff Empty Bool := ⟨fun _ => true⟩
  exact .let₁ (.let₂ .var .var) (.case .var (.inr .var) (.inl .var))

private theorem he : ValueBranches [] entry [state, out] :=
  .br (ℓ := 0) rfl (.pair .unit (.inr .unit))

private theorem nextState_typed (Γ : VCtx Types) : Tm.HasType Γ nextState bit :=
  .let₁ (.let₂ (.pair .unit (.inl .unit)) (.var (i := 0) rfl)) (flip_typed _)

private theorem hp : ValueBranches [state] sourceStep [state, out] :=
  .let₁ ht (.case (.var (i := 0) rfl)
    (.br (ℓ := 0) rfl (.pair .unit (.inl .unit))) (.br (ℓ := 1) rfl .unit))

private theorem hq : ValueBranches [bit] targetStep [bit, out] :=
  .case (.var (i := 0) rfl)
    (.let₁ (nextState_typed _) (.br (ℓ := 0) rfl (.var (i := 0) rfl))) (.br (ℓ := 1) rfl .unit)

private theorem local_comm :
    Paper.Eqv [state] (sourceStep.lsubst (liftLSubstVars (boundLocalMap changeState)))
      ((Region.br 0 changeState).bindBranchArguments.lsubst
        (liftLSubstVars (fun _ => targetStep))) [bit, out] := by
  rw [lsubst_bindBranchArguments_br]
  apply Paper.Eqv.refl
  exact .let₁ ht (.case (.var (i := 0) rfl)
    (.let₁ (nextState_typed _) (.br (ℓ := 0) rfl (.var (i := 0) rfl))) (.br (ℓ := 1) rfl .unit))

private theorem bound_comm :
    stepArrow hp ≫ coprod.map (𝟙 (ofType out)) (boundReturn ht) =
      boundReturn ht ≫ stepArrow hq :=
  (ordinary_square_iff hp hq ht).2 local_comm

private theorem feedbackStep :
    InstructionFreeStep [] (.cfg entry 1 (fun _ => sourceStep))
      (.cfg (entry.lsubst (boundLocalMap changeState)) 1 (fun _ => targetStep)) [out] :=
  instructionFreeStep_of_ordinary_square he hp hq ht free bound_comm

private abbrev Seed (Γ : VCtx Types) (r s : Region Empty) (L : LCtx Types) : Prop :=
  UnaryReturn.Step Γ r s L ∨ InstructionFreeStep Γ r s L

local notation "F" => Paper.Extension.Singleton.projection Seed

theorem state_change_eq :
    (F).map (returnTerm ht) = (F).map (boundReturn ht) :=
  UnaryReturn.mapped_returnTerm_eq_boundReturn (fun e => Or.inl e) ht

theorem cfg_eq :
    Paper.Extension.Eqv Seed [] (.cfg entry 1 (fun _ => sourceStep))
      (.cfg (entry.lsubst (boundLocalMap changeState)) 1 (fun _ => targetStep)) [out] :=
  .extra feedbackStep.typed.1 feedbackStep.typed.2 (.inr feedbackStep)

end UnaryStateChange

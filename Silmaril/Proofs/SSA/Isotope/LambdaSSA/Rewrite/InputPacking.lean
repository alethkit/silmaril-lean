module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheorySubstitution

/-! # Formation of packed value inputs -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

omit [HasTy Φ τ] in
theorem packedInputValue_branchValue (Γ : VCtx τ) :
    Tm.BranchValue Γ (packedInputValue Γ : Tm Φ) (packedInputType Γ) := by
  induction Γ with
  | nil => exact .unit
  | cons A Γ ih =>
    exact .pair (branchValue_rename ih (Ren.wk Γ A)) (.var (i := 0) rfl)

theorem packedInputProjection_hasType {Γ Δ : VCtx τ} {i : Nat} {A : τ} {a : Tm Φ}
    (hi : At Γ i A) (ha : Tm.HasType Δ a (packedInputType Γ)) :
    Tm.HasType Δ (packedInputProjection i a) A := by
  induction Γ generalizing i A a with
  | nil => simp [At] at hi
  | cons B Γ ih =>
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact .let₂ ha (.var (i := 0) rfl)
    | succ i => exact ih (i := i) hi (.let₂ ha (.var (i := 1) rfl))

omit [HasTy Φ τ] in
theorem unpackInputs_subst {Γ : VCtx τ} {i : Nat} {A : τ}
    (hi : At [packedInputType Γ] i A) :
    Tm.BranchValue Γ (Tm.singleSubst (packedInputValue Γ : Tm Φ) i) A := by
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact packedInputValue_branchValue Γ
  | succ i =>
    simp [At] at hi

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

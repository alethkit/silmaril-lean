module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution

/-! # Simultaneous transport along constructor-valued substitutions -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory (fst snd lift toUnit)

set_option backward.isDefEq.respectTransparency false

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

private theorem substDenotes_of_branchValues {Γ Δ : VCtx τ} {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (σ i) A) :
    ∃ k : ctxObj M Δ ⟶ ctxObj M Γ, SubstDenotes J M σ k := by
  induction Γ generalizing σ with
  | nil =>
    refine ⟨toUnit _, ?_⟩
    intro i A hi
    simp [At] at hi
  | cons B Γ ih =>
    obtain ⟨k, dk⟩ := ih (σ := fun i => σ (i + 1)) (fun _ _ hi => hσ hi)
    obtain ⟨p, dp⟩ := (hσ (show At (B :: Γ) 0 B from rfl)).denotes_map J M
    refine ⟨lift k p, ?_⟩
    intro i A hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      change ∃ h : Tm.HasType Δ (σ 0) B,
        Denotes J M h (J.map (lift k p ≫ lookup M 0 (rfl : At (B :: Γ) 0 B)))
      simp only [lookup, CartesianMonoidalCategory.lift_snd]
      exact ⟨(hσ hi).hasType, dp⟩
    | succ i =>
      change ∃ h : Tm.HasType Δ (σ (i + 1)) A,
        Denotes J M h (J.map (lift k p ≫ fst (ctxObj M Γ) (M.obj B) ≫ lookup M i hi))
      rw [CartesianMonoidalCategory.lift_fst_assoc]
      exact dk hi

theorem substBranchValues {Γ Δ : VCtx τ} {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (σ i) A) :
    ∃ k : ctxObj M Δ ⟶ ctxObj M Γ,
      ∀ {L : LCtx τ} {r : Region Φ} {hr : Region.HasType Γ r L}
        {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)},
        RegionDenotes J M hr f →
          ∃ ht : Region.HasType Δ (r.substVars σ) L, RegionDenotes J M ht (J.map k ≫ f) := by
  obtain ⟨k, dk⟩ := substDenotes_of_branchValues J M hσ
  exact ⟨k, fun d => regionDenotes_subst J M d dk⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Composition.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.EnvironmentNaturality

/-! # Categorical composition of linked continuation families -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory.CartesianMonoidalCategory (fst)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem continuationDenotes_liftVars {Γ : VCtx τ} {L K : LCtx τ}
    {σ : Nat → Region Φ} {k : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    (hk : ContinuationDenotes J M σ k) (A : τ) :
    ContinuationDenotes J M (Γ := A :: Γ) (L := L) (K := K) (Region.liftLSubstVars σ)
      (J.map (fst (ctxObj M Γ) (M.obj A) ▷ labelObj M L) ≫ k) := by
  intro i B hi
  obtain ⟨h, d⟩ := hk hi
  have w := regionDenotes_weakenCapture J M (B := A) d
  refine ⟨h.renameVars ((Silmaril.Isotope.SSA.Ren.wk Γ A).lift B), ?_⟩
  simp only [MonoidalCategory.id_tensorHom] at w ⊢
  rw [← J.map_comp_assoc, MonoidalCategory.whisker_exchange, J.map_comp_assoc]
  exact w

variable [FreydCategory.CentralUnit J]

set_option backward.isDefEq.respectTransparency false in
theorem continuationDenotes_linkComp {Γ : VCtx τ} {L K H : LCtx τ}
    {σ υ : Nat → Region Φ}
    {first : J.obj (ctxObj M Γ ⊗ labelObj M L) ⟶ J.obj (labelObj M K)}
    {after : J.obj (ctxObj M Γ ⊗ labelObj M K) ⟶ J.obj (labelObj M H)}
    (df : ContinuationDenotes J M σ first) (dg : ContinuationDenotes J M υ after) :
    ContinuationDenotes J M (Region.linkCompLSubst K σ υ)
      (composeContinuations J M (Γ := Γ) (L := L) (K := K) (H := H) first after) := by
  intro i A hi
  obtain ⟨_, d⟩ := df hi
  have dw := continuationDenotes_liftVars J M dg A
  obtain ⟨hs, ds⟩ := d.linkExits J M dw
  change Region.HasType (A :: Γ) (Region.linkCompLSubst K σ υ i) H at hs
  refine ⟨hs, ?_⟩
  let E := ctxObj M Γ
  let j := E ◁ labelInject M i hi
  let q := fst E (M.obj A)
  let p := fst E (labelObj M L)
  let X := labelObj M K
  have hq : (j ▷ X) ≫ (p ▷ X) = q ▷ X := by
    rw [← MonoidalCategory.comp_whiskerRight, CartesianMonoidalCategory.whiskerLeft_fst]
  simp only [composeContinuations, MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
  change RegionDenotes J M hs (J.map j ≫
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J first (J.map (p ▷ X) ≫ after))
  rw [← bind_pre_map, ← J.map_comp_assoc, hq]
  simpa only [MonoidalCategory.id_tensorHom] using ds

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

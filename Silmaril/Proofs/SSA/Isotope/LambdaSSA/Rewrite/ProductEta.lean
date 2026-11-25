module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

/-! # Product η in the categorical denotation graph -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductEta

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel extend_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (retainedContext duplicate)

universe v₁ v₂ u₁ u₂ u₃ u₄

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "extendArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.extend
local notation "pairArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair

local notation "U" => Functor.StrongPremonoidal.unitIso (J := J)

section Freyd
variable [DistributiveFreydCategory J]

private theorem extend_repack_snd (hu : IsCentral (U).hom) {E P : V}
    (f : J.obj E ⟶ J.obj P) : extendArrow J f ≫ J.map (snd E P) = f := by
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.extend, leftTensor, id_whiskerRight, Category.id_comp, Category.assoc]
  rw [FreydCategory.whiskerLeft_snd_of_unit_central J hu, ← J.map_comp_assoc]
  simp [duplicate]

private theorem pair_of_maps {E X Y : V} (p : E ⟶ X) (q : E ⟶ Y) :
    pairArrow J (J.map p) (J.map q) = J.map (lift p q) := by
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair,
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, retainedContext, extend_map, ← J.map_comp]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

end Freyd

private noncomputable def rebuild (Γ : VCtx τ) (A B : τ) :
    ctxObj M (B :: A :: Γ) ⟶ M.obj (Silmaril.product A B) :=
  lift (lookup M 1 (rfl : At (B :: A :: Γ) 1 A))
    (lookup M 0 (rfl : At (B :: A :: Γ) 0 B)) ≫ (M.productIso A B).inv

omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C] in
private theorem unpack_rebuild (Γ : VCtx τ) (A B : τ) :
    ((𝟙 (ctxObj M Γ)) ⊗ₘ (M.productIso A B).hom) ≫
      (ctxPairIso M Γ A B).hom ≫ rebuild M Γ A B =
    snd (ctxObj M Γ) (M.obj (Silmaril.product A B)) := by
  have hpair : (ctxPairIso M Γ A B).hom ≫
      lift (lookup M 1 (rfl : At (B :: A :: Γ) 1 A))
        (lookup M 0 (rfl : At (B :: A :: Γ) 0 B)) =
      snd (ctxObj M Γ) (M.obj A ⊗ M.obj B) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [ctxPairIso, Iso.symm_hom, Category.assoc, lift_fst, lookup, ctxObj, associator_inv_fst_snd]
    · simp only [ctxPairIso, Iso.symm_hom, Category.assoc, lift_snd, lookup, ctxObj, associator_inv_snd]
  unfold rebuild
  rw [← Category.assoc (ctxPairIso M Γ A B).hom, hpair, tensorHom_snd_assoc, Iso.hom_inv_id, Category.comp_id]

section Terms
variable [DistributiveFreydCategory J]

set_option backward.isDefEq.respectTransparency false in
private theorem rebuild_denotes (Γ : VCtx τ) (A B : τ) :
    Denotes J M (Φ := Φ) (.pair (.var (i := 1) (rfl : At (B :: A :: Γ) 1 A))
      (.var (i := 0) (rfl : At (B :: A :: Γ) 0 B))) (J.map (rebuild M Γ A B)) := by
  have h := Denotes.pair
    (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 1) (rfl : At (B :: A :: Γ) 1 A))
    (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At (B :: A :: Γ) 0 B))
  simpa only [pair_of_maps, ← J.map_comp, rebuild] using h

private theorem bind_rebuild {Γ : VCtx τ} {A B : τ} {Z : V}
    (f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B)))
    (k : J.obj (M.obj (Silmaril.product A B)) ⟶ J.obj Z)
    (drop : extendArrow J f ≫ J.map (snd (ctxObj M Γ) (M.obj (Silmaril.product A B))) = f) :
    bindArrow J f (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ (M.productIso A B).hom) ≫
      J.map (ctxPairIso M Γ A B).hom ≫ J.map (rebuild M Γ A B) ≫ k) = f ≫ k := by
  rw [← J.map_comp_assoc, ← J.map_comp_assoc, Category.assoc, unpack_rebuild]
  rw [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, ← Category.assoc, drop]

set_option backward.isDefEq.respectTransparency false in
private theorem expression_eta {Γ : VCtx τ} {a : Tm Φ} {A B : τ}
    {ha : Tm.HasType Γ a (Silmaril.product A B)}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B))}
    (da : Denotes J M ha f)
    (drop : extendArrow J f ≫ J.map (snd (ctxObj M Γ) (M.obj (Silmaril.product A B))) = f) :
    Denotes J M (.let₂ ha (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))) f := by
  have h := Denotes.let₂ da (rebuild_denotes (Φ := Φ) J M Γ A B)
  have eta := bind_rebuild J M f (𝟙 _) drop
  simp only [Category.comp_id] at eta
  rw [eta] at h
  exact h

/-- The paper's expression product η keeps the same structural arrow,
including when the scrutinee is effectful. -/
theorem term_eta (hu : IsCentral (U).hom) {Γ : VCtx τ} {a : Tm Φ} {A B : τ}
    {ha : Tm.HasType Γ a (Silmaril.product A B)}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B))} (da : Denotes J M ha f) :
    Denotes J M (.let₂ ha (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))) f :=
  expression_eta J M da (extend_repack_snd J hu f)

end Terms

section Regions
variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

set_option backward.isDefEq.respectTransparency false in
private theorem region_eta {Γ : VCtx τ} {a : Tm Φ} {A B : τ} {L : LCtx τ} {i : Nat}
    {ha : Tm.HasType Γ a (Silmaril.product A B)}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B))}
    (hi : At L i (Silmaril.product A B)) (da : Denotes J M ha f)
    (drop : extendArrow J f ≫ J.map (snd (ctxObj M Γ) (M.obj (Silmaril.product A B))) = f) :
    RegionDenotes J M (.let₂ ha (.br hi (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))
      (f ≫ J.map (labelInject M i hi)) := by
  have h := RegionDenotes.let₂ da (RegionDenotes.br (h := hi) (rebuild_denotes (Φ := Φ) J M Γ A B))
  rw [bind_rebuild J M f (J.map (labelInject M i hi)) drop] at h
  exact h

/-- Destructuring and repacking a scrutinee before branching keeps the
structural arrow of branching directly on the scrutinee. -/
theorem branch_eta (hu : IsCentral (U).hom) {Γ : VCtx τ} {a : Tm Φ}
    {A B : τ} {L : LCtx τ} {i : Nat} {ha : Tm.HasType Γ a (Silmaril.product A B)}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (Silmaril.product A B))}
    (hi : At L i (Silmaril.product A B)) (da : Denotes J M ha f) :
    RegionDenotes J M (.let₂ ha (.br hi (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))
      (f ≫ J.map (labelInject M i hi)) :=
  region_eta J M hi da (extend_repack_snd J hu f)

/-- A value-map scrutinee needs no centrality premise on the unit comparison. -/
theorem branch_eta_of_map {Γ : VCtx τ} {a : Tm Φ} {A B : τ} {L : LCtx τ}
    {i : Nat} {ha : Tm.HasType Γ a (Silmaril.product A B)}
    {p : ctxObj M Γ ⟶ M.obj (Silmaril.product A B)} (hi : At L i (Silmaril.product A B))
    (da : Denotes J M ha (J.map p)) :
    RegionDenotes J M (.let₂ ha (.br hi (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))
      (J.map p ≫ J.map (labelInject M i hi)) := by
  apply region_eta J M hi da
  rw [extend_map, ← J.map_comp, lift_snd]

end Regions

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ProductEta

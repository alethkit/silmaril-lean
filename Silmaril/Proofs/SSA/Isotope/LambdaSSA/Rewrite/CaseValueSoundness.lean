module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution

/-! # Categorical soundness of case analysis at a sum value -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext extend splitMapCoprod)
open CategoryTheory.CartesianMonoidalCategory (snd lift)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

private theorem caseOfValue (J : V ⥤ C) [DistributiveFreydCategory J]
    {E A B S D : V} (e : S ≅ A ⨿ B) (p : E ⟶ S)
    (f : J.obj (E ⊗ S) ⟶ J.obj D) :
    caseWithContext J (J.map p ≫ J.map e.hom)
      (J.map (E ◁ (coprod.inl ≫ e.inv)) ≫ f) (J.map (E ◁ (coprod.inr ≫ e.inv)) ≫ f) =
      J.map (lift (𝟙 E) p) ≫ f := by
  let route := J.map (DistributiveTensor.leftIso E A B).inv ≫ splitMapCoprod J (E ⊗ A) (E ⊗ B)
  have instRoute : IsIso route := by unfold route splitMapCoprod; infer_instance
  have hroute : route ≫ coprod.desc (J.map (E ◁ (coprod.inl ≫ e.inv)) ≫ f)
      (J.map (E ◁ (coprod.inr ≫ e.inv)) ≫ f) = J.map (E ◁ e.inv) ≫ f := by
    apply (cancel_epi (inv route)).mp
    rw [IsIso.inv_hom_id_assoc]
    apply coprod.hom_ext
    · have hi : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) := by
        have h : J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ route = coprod.inl :=
          distributeMap_inl J E A B
        rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [coprod.inl_desc, ← Category.assoc, hi, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp]
    · have hi : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) := by
        have h : J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ route = coprod.inr :=
          distributeMap_inr J E A B
        rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [coprod.inr_desc, ← Category.assoc, hi, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp]
  unfold caseWithContext Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
  rw [← Category.assoc (J.map (DistributiveTensor.leftIso E A B).inv)]
  change extend J (J.map p ≫ J.map e.hom) ≫ (route ≫ _) = _
  rw [hroute, extend_post_map, Category.assoc, ← J.map_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id,
    J.map_id, Category.id_comp, extend_map]

variable [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem caseValue_common {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {a : Tm Φ} {A B : τ}
    (ha : Tm.BranchValue Γ a (Silmaril.coprod A B)) (hr : Region.HasType (Silmaril.coprod A B :: Γ) r L) :
    ∃ (hl : Region.HasType Γ
        (.case a (r.substVars (Tm.replaceNewest (.inl (.var 0))))
          (r.substVars (Tm.replaceNewest (.inr (.var 0))))) L)
      (ht : Region.HasType Γ (r.substVars (Tm.singleSubst a)) L), ∃ f,
      RegionDenotes J M hl f ∧ RegionDenotes J M ht f := by
  let E := ctxObj M Γ
  let e := M.coprodIso A B
  let i₁ := (coprod.inl : M.obj A ⟶ M.obj A ⨿ M.obj B) ≫ e.inv
  let i₂ := (coprod.inr : M.obj B ⟶ M.obj A ⨿ M.obj B) ≫ e.inv
  obtain ⟨p, da⟩ := ha.denotes_map J M
  obtain ⟨f, dr⟩ := regionDenotes_exists J M hr
  have dl : Denotes J M (.inl (B := B) (.var (Φ := Φ) (Γ := A :: Γ) (i := 0) (A := A) rfl))
      (J.map (snd E (M.obj A) ≫ i₁)) := by
    rw [J.map_comp]
    exact .inl (.var (i := 0) rfl)
  have ds : Denotes J M (.inr (A := A) (.var (Φ := Φ) (Γ := B :: Γ) (i := 0) (A := B) rfl))
      (J.map (snd E (M.obj B) ≫ i₂)) := by
    rw [J.map_comp]
    exact .inr (.var (i := 0) rfl)
  obtain ⟨_, dl'⟩ := regionDenotes_replaceNewest J M dr dl
  obtain ⟨_, ds'⟩ := regionDenotes_replaceNewest J M dr ds
  obtain ⟨_, dt⟩ := regionDenotes_substValue_proof J M dr da
  have dcase := RegionDenotes.case da dl' ds'
  rw [caseOfValue J e p f] at dcase
  exact ⟨_, _, _, dcase, dt⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

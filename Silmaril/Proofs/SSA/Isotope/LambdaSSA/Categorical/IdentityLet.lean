module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Let.Identity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

/-! # Identity lets in distributive premonoidal models -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.IdentityLet

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open CategoryTheory.CartesianMonoidalCategory (snd)
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel extend_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind extend duplicate)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] (J : V ⥤ C)

local notation "U" => Functor.StrongPremonoidal.unitIso (J := J)

section Bind

variable [FreydCategory J]

private theorem extend_snd (hu : IsCentral (U).hom) {R A : V} (f : J.obj R ⟶ J.obj A) :
    extend J f ≫ J.map (snd R A) = f := by
  simp only [extend, leftTensor, id_whiskerRight, Category.id_comp, Category.assoc]
  rw [FreydCategory.whiskerLeft_snd_of_unit_central J hu, ← J.map_comp_assoc]
  simp [duplicate]

private theorem extend_map_snd {R A : V} (p : R ⟶ A) :
    extend J (J.map p) ≫ J.map (snd R A) = J.map p := by
  rw [extend_map J, ← J.map_comp, CartesianMonoidalCategory.lift_snd]

end Bind

variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [DistributiveFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

private theorem termOfProjection {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    {ht : Tm.HasType Γ t A} {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (d : Denotes J M ht f) (project : extend J f ≫ J.map (snd (ctxObj M Γ) (M.obj A)) = f) :
    Denotes J M (.let₁ ht (.var (i := 0) rfl)) f := by
  have bound := Denotes.let₁ d (Denotes.var (i := 0) (show At (A :: Γ) 0 A from rfl))
  change Denotes J M (.let₁ ht (.var (i := 0) rfl))
    (extend J f ≫ J.map (snd (ctxObj M Γ) (M.obj A))) at bound
  exact project ▸ bound

theorem term (hu : IsCentral (U).hom) {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    {ht : Tm.HasType Γ t A} {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (d : Denotes J M ht f) : Denotes J M (.let₁ ht (.var (i := 0) rfl)) f :=
  termOfProjection J M d (extend_snd J hu f)

theorem termOfMap {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    {ht : Tm.HasType Γ t A} {p : ctxObj M Γ ⟶ M.obj A}
    (d : Denotes J M ht (J.map p)) : Denotes J M (.let₁ ht (.var (i := 0) rfl)) (J.map p) :=
  termOfProjection J M d (extend_map_snd J p)

theorem inContext (hu : IsCentral (U).hom) {Γ : VCtx τ} {s t : Tm Φ} {A : τ}
    {hs : Tm.HasType Γ s A} {ht : Tm.HasType Γ t A} (h : Tm.IdentityLet hs ht) :
    ∃ f, Denotes J M hs f ∧ Denotes J M ht f := by
  induction h with
  | same h =>
    obtain ⟨f, d⟩ := denotes_exists J M h
    exact ⟨f, d, d⟩
  | remove h =>
    obtain ⟨f, d⟩ := denotes_exists J M h
    exact ⟨f, term J M hu d, d⟩
  | op _ ih =>
    obtain ⟨_, dl, dr⟩ := ih
    exact ⟨_, .op dl, .op dr⟩
  | let₁ _ _ ih1 ih2 =>
    obtain ⟨_, dl, dr⟩ := ih1
    obtain ⟨_, el, er⟩ := ih2
    exact ⟨_, .let₁ dl el, .let₁ dr er⟩
  | pair _ _ ih1 ih2 =>
    obtain ⟨_, dl, dr⟩ := ih1
    obtain ⟨_, el, er⟩ := ih2
    exact ⟨_, .pair dl el, .pair dr er⟩
  | let₂ _ _ ih1 ih2 =>
    obtain ⟨_, dl, dr⟩ := ih1
    obtain ⟨_, el, er⟩ := ih2
    exact ⟨_, .let₂ dl el, .let₂ dr er⟩
  | inl _ ih =>
    obtain ⟨_, dl, dr⟩ := ih
    exact ⟨_, .inl dl, .inl dr⟩
  | inr _ ih =>
    obtain ⟨_, dl, dr⟩ := ih
    exact ⟨_, .inr dl, .inr dr⟩
  | case _ _ _ ih1 ih2 ih3 =>
    obtain ⟨_, dl, dr⟩ := ih1
    obtain ⟨_, el, er⟩ := ih2
    obtain ⟨_, fl, fr⟩ := ih3
    exact ⟨_, .case dl el fl, .case dr er fr⟩
  | abort _ ih =>
    obtain ⟨_, dl, dr⟩ := ih
    exact ⟨_, .abort dl, .abort dr⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.IdentityLet

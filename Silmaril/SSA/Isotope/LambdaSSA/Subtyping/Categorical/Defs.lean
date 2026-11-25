module

public import Silmaril.SSA.Isotope.LambdaSSA.Subtyping.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Categorical denotation of subtyped λSSA -/

@[expose] public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
  (ctxObj lookup ctxPairIso labelObj labelInject finiteLabelObj labelObjToFinite
    labelAppendSplit CollectiveDenotes)

/-- The subtyping model's underlying exact type interpretation. -/
abbrev exactTypeModel {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V]
    [HasFiniteCoproducts V] {τ : Type u₃} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ]
    (M : TypeModel τ V) : Silmaril.Isotope.LetIter.Semantics.Categorical.TypeModel τ V where
  obj := M.obj
  productIso := M.productIso
  unitIso := M.unitIso
  coprodIso := M.coprodIso
  emptyIsInitial := M.emptyIsInitial

section Term

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ]
  (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Direct categorical interpretation.  In particular, `.sub h d` is
interpreted by the specific morphism `M.subty d`. -/
noncomputable def denote : {Γ : VCtx τ} → {t : LambdaSSA.Tm Φ} → {A : τ} →
    Tm.HasType Γ t A → (J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (M.obj A))
  | _, _, _, .var h => J.map (lookup (exactTypeModel M) _ h)
  | _, _, _, .op h => denote h ≫ InstructionModel.denote _
  | _, _, _, .let₁ ha hb => bind J (denote ha) (denote hb)
  | _, _, _, .pair ha hb =>
      pair J (denote ha) (denote hb) ≫ J.map (M.productIso _ _).inv
  | _, _, _, .unit =>
      J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv)
  | _, _, _, .let₂ ha hb =>
      bind J (denote ha) <|
        J.map ((𝟙 _) ⊗ₘ (M.productIso _ _).hom) ≫
          J.map (ctxPairIso (exactTypeModel M) _ _ _).hom ≫ denote hb
  | _, _, _, .inl ha =>
      denote ha ≫ J.map (coprod.inl ≫ (M.coprodIso _ _).inv)
  | _, _, _, .inr hb =>
      denote hb ≫ J.map (coprod.inr ≫ (M.coprodIso _ _).inv)
  | _, _, _, .case he hl hr =>
      caseWithContext J (denote he ≫ J.map (M.coprodIso _ _).hom)
        (denote hl) (denote hr)
  | _, _, _, .abort ha => abort J M (denote ha)
  | _, _, _, .sub ha d => denote ha ≫ J.map (M.subty d)

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Structural graph of the proof-relevant categorical term semantics. -/
inductive Denotes : {Γ : VCtx τ} → {t : LambdaSSA.Tm Φ} → {A : τ} →
    Tm.HasType Γ t A → (J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (M.obj A)) → Prop where
  | var (h : At Γ i A) : Denotes (.var h) (J.map (lookup (exactTypeModel M) i h))
  | op (dha : Denotes ha fa) : Denotes (.op ha) (fa ≫ InstructionModel.denote _)
  | let₁ (dha : Denotes ha fa) (dhb : Denotes hb fb) :
      Denotes (.let₁ ha hb) (bind J fa fb)
  | pair (dha : Denotes ha fa) (dhb : Denotes hb fb) :
      Denotes (.pair ha hb) (pair J fa fb ≫ J.map (M.productIso _ _).inv)
  | unit : Denotes (.unit (Γ := Γ))
      (J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv))
  | let₂ (dha : Denotes ha fa) (dhb : Denotes hb fb) :
      Denotes (.let₂ ha hb) (bind J fa (
        J.map ((𝟙 _) ⊗ₘ (M.productIso _ _).hom) ≫
          J.map (ctxPairIso (exactTypeModel M) _ _ _).hom ≫ fb))
  | inl (dha : Denotes ha fa) : Denotes (.inl (B := B) ha)
      (fa ≫ J.map (coprod.inl ≫ (M.coprodIso _ _).inv))
  | inr (dhb : Denotes hb fb) : Denotes (.inr (A := A) hb)
      (fb ≫ J.map (coprod.inr ≫ (M.coprodIso _ _).inv))
  | case (dhe : Denotes he fe) (dhl : Denotes hl fl) (dhr : Denotes hr fr) :
      Denotes (.case he hl hr)
        (caseWithContext J (fe ≫ J.map (M.coprodIso _ _).hom) fl fr)
  | abort (dha : Denotes ha fa) :
      Denotes (.abort (A := A) ha) (abort J M fa)
  | sub {A B : τ} {ha : Tm.HasType Γ a A}
      {fa : J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (M.obj A)}
      (dha : Denotes ha fa) (d : Silmaril.Isotope.Subty A B) :
      Denotes (.sub ha d) (fa ≫ J.map (M.subty d))

end Term

section Region

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ]
  (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Structural denotation graph.  Unlike exact SSA, its term premises use the
proof-relevant denotation and therefore retain every coercion witness. -/
inductive RegionDenotes : {Γ : VCtx τ} → {r : LambdaSSA.Region Φ} → {L : LCtx τ} →
    Region.HasType Γ r L → (J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (labelObj (exactTypeModel M) L)) → Prop where
  | br (dt : Denotes J M ha fa) : RegionDenotes (.br h ha)
      (fa ≫ J.map (labelInject (exactTypeModel M) _ h))
  | case (de : Denotes J M he fe)
      (dl : RegionDenotes hl fl) (dr : RegionDenotes hr fr) :
      RegionDenotes (.case he hl hr)
        (caseWithContext J
          (fe ≫ J.map (M.coprodIso _ _).hom) fl fr)
  | let₁ (da : Denotes J M ha fa) (db : RegionDenotes hb fb) :
      RegionDenotes (.let₁ ha hb) (bind J fa fb)
  | let₂ (da : Denotes J M ha fa) (db : RegionDenotes hb fb) :
      RegionDenotes (.let₂ ha hb) (bind J fa (
        J.map ((𝟙 _) ⊗ₘ (M.productIso _ _).hom) ≫
          J.map (ctxPairIso (exactTypeModel M) _ _ _).hom ≫ fb))
  | cfgZero {R : Fin 0 → τ} {entry : LambdaSSA.Region Φ}
      {blocks : Fin 0 → LambdaSSA.Region Φ}
      {he : Region.HasType Γ entry (List.ofFn R ++ L)}
      {hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)}
      {fe : J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (labelObj (exactTypeModel M) L)}
      (de : RegionDenotes he fe) :
      RegionDenotes (.cfg R he hb) fe
  | cfg {n : Nat} {R : Fin (n + 1) → τ} {Γ : VCtx τ} {L : LCtx τ}
      {entry : LambdaSSA.Region Φ} {blocks : Fin (n + 1) → LambdaSSA.Region Φ}
      {he : Region.HasType Γ entry (List.ofFn R ++ L)}
      {hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)}
      {fe : J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (labelObj (exactTypeModel M) (List.ofFn R ++ L))}
      {fb : ∀ i, J.obj (ctxObj (exactTypeModel M) (R i :: Γ)) ⟶
        J.obj (labelObj (exactTypeModel M) (List.ofFn R ++ L))}
      {collective : J.obj (ctxObj (exactTypeModel M) Γ ⊗ finiteLabelObj (exactTypeModel M) R) ⟶
        J.obj (labelObj (exactTypeModel M) (List.ofFn R ++ L))}
      (de : RegionDenotes he fe)
      (db : ∀ i, RegionDenotes (hb i) (fb i))
      (dc : LambdaSSA.Semantics.Categorical.CollectiveDenotes J (exactTypeModel M) Γ R L fb collective) :
      RegionDenotes (.cfg R he hb) (caseWithContext J
        (fe ≫ J.map (labelAppendSplit (exactTypeModel M) (List.ofFn R) L))
        (J.map (CartesianMonoidalCategory.snd _ _))
        (contextualLoop J
          (J.map ((𝟙 (ctxObj (exactTypeModel M) Γ)) ⊗ₘ labelObjToFinite (exactTypeModel M) R) ≫
            collective ≫ J.map (labelAppendSplit (exactTypeModel M) (List.ofFn R) L))))

/-- Optional coherence for proof-relevant region typing derivations. -/
class RegionTypingCoherent : Prop where
  denotes_eq {Γ : VCtx τ} {r : LambdaSSA.Region Φ} {L : LCtx τ}
      {h : Region.HasType Γ r L}
      {f g : J.obj (ctxObj (exactTypeModel M) Γ) ⟶ J.obj (labelObj (exactTypeModel M) L)} :
      RegionDenotes J M h f → RegionDenotes J M h g → f = g

end Region

end Silmaril.Isotope.LambdaSSA.Subtyping.Semantics.Categorical

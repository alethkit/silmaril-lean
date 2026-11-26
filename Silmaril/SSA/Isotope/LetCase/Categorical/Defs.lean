module

public import Silmaril.SSA.Isotope.LetCase.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms

/-! # Exact LetCase denotation in distributive Freyd categories -/

@[expose] public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetCase

open LocallyNameless

namespace LocallyNameless.Derivation

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}

/-- Rename an exact derivation while keeping its intermediate types. -/
def rename {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (ρ : BoundCtx.Renaming β δ) :
    {t : Tm ν Φ n} → {A : τ} → Derivation Φ Γ β t A →
      Derivation Φ Γ δ (t.rename ρ.toFun) A
  | _, _, .fv h => .fv h
  | _, _, .bv (ι := i) => ρ.typed i ▸ .bv
  | _, _, .op h => .op (rename ρ h)
  | _, _, .let₁ h k => .let₁ (rename ρ h) (rename (ρ.up _) k)
  | _, _, .unit => .unit
  | _, _, .pair h k => .pair (rename ρ h) (rename ρ k)
  | _, _, .let₂ h k => .let₂ (rename ρ h) (rename ((ρ.up _).up _) k)
  | _, _, .inl h => .inl (rename ρ h)
  | _, _, .inr h => .inr (rename ρ h)
  | _, _, .case h l r => .case (rename ρ h) (rename (ρ.up _) l) (rename (ρ.up _) r)
  | _, _, .abort h => .abort (rename ρ h)

/-- Insert a slot below the result binder, leaving the result at index zero. -/
def underBinder {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 1)} {X Y A : τ}
    (d : Derivation Φ Γ (β.snoc Y) t A) :
    Derivation Φ Γ ((β.snoc X).snoc Y) t.underBinder A :=
  d.rename (BoundCtx.Renaming.underBinder β X Y)

end LocallyNameless.Derivation

namespace Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj freeLookup boundVar envSnocIso envPairHom)
open LetIter.ProofRelevant.Semantics.Categorical (bind pair caseWithContext)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type w} [DecidableEq ν] {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Interpret exact LetCase derivations using the shared Freyd context and
instruction models. The syntax needs only sequencing and coproducts. -/
noncomputable def denote : {Γ : Ctx ν τ} → {n : Nat} →
    {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
    Derivation Φ Γ β t A → (J.obj (envObj M Γ β) ⟶ J.obj (M.obj A))
  | _, _, _, _, _, .fv h => J.map (freeLookup M _ h)
  | _, _, _, _, _, .bv => J.map (boundVar M _)
  | _, _, _, _, _, .op ha => denote ha ≫ InstructionModel.denote _
  | Γ, _, β, _, _, .let₁ ha hb => bind J (denote ha) <|
      J.map (envSnocIso M Γ β _).hom ≫ denote hb
  | _, _, _, _, _, .unit =>
      J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv)
  | _, _, _, _, _, .pair ha hb =>
      pair J (denote ha) (denote hb) ≫ J.map (M.productIso _ _).inv
  | Γ, _, β, _, _, .let₂ ha hc => bind J (denote ha) <|
      J.map ((𝟙 _) ⊗ₘ (M.productIso _ _).hom) ≫
        J.map (envPairHom M Γ β _ _) ≫ denote hc
  | _, _, _, _, _, .inl ha =>
      denote ha ≫ J.map (coprod.inl ≫ (M.coprodIso _ _).inv)
  | _, _, _, _, _, .inr hb =>
      denote hb ≫ J.map (coprod.inr ≫ (M.coprodIso _ _).inv)
  | Γ, _, β, _, _, .case he hl hr =>
      caseWithContext J (denote he ≫ J.map (M.coprodIso _ _).hom)
        (J.map (envSnocIso M Γ β _).hom ≫ denote hl)
        (J.map (envSnocIso M Γ β _).hom ≫ denote hr)
  | _, _, _, _, _, .abort ha =>
      denote ha ≫ J.map (M.emptyIsInitial.to (M.obj _))

/-- Independence of the chosen exact typing derivation at a fixed judgment.
The continuation law at its constructed witnesses does not need this. -/
def TypingCoherent (ν : Type w) [DecidableEq ν] (Φ : Type v) [HasTy Φ τ]
    [InstructionModel J M Φ] : Prop :=
  ∀ {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d d' : Derivation Φ Γ β t A), denote J M d = denote J M d'

end Semantics.Categorical
end Silmaril.Isotope.LetCase

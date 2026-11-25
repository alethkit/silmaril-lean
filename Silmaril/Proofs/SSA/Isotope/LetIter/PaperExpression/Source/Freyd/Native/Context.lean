module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Defs

public section

universe u w u₁ v₁

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Proofs

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Semantics.Categorical (TypeModel boundObj boundLookup boundVar envObj ctxObj envSnocIso envPairHom)

variable {τ : Type u} {ε : Type w} [TypeFormers τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]

theorem projection_transport (M : TypeModel τ V) (Γ : EffectCtx τ ε) (i : Fin Γ.length) :
    Freyd.projection M Γ i =
      (packedTypeIso M Γ).hom ≫ boundLookup M (β := (EffectCtx.toBoundCtx Γ)) i ≫
        eqToHom (congrArg M.obj (EffectCtx.get_toBoundCtx Γ i)) := by
  induction Γ with
  | nil => exact i.elim0
  | cons slot Γ ih =>
    obtain ⟨A, e⟩ := slot
    refine Fin.cases ?_ (fun j => ?_) i
    · change (M.productIso (packType Γ) A).hom ≫ snd _ _ =
        ((M.productIso (packType Γ) A).hom ≫
          ((packedTypeIso M Γ).hom ⊗ₘ 𝟙 (M.obj A))) ≫
            snd (boundObj M (EffectCtx.toBoundCtx Γ)) (M.obj A) ≫ 𝟙 (M.obj A)
      simp
    · change (M.productIso (packType Γ) A).hom ≫
          fst (M.obj (packType Γ)) (M.obj A) ≫ Freyd.projection M Γ j =
        ((M.productIso (packType Γ) A).hom ≫
          ((packedTypeIso M Γ).hom ⊗ₘ 𝟙 (M.obj A))) ≫
            (fst (boundObj M (EffectCtx.toBoundCtx Γ)) (M.obj A) ≫ boundLookup M (β := (EffectCtx.toBoundCtx Γ)) j) ≫
            eqToHom (congrArg M.obj (EffectCtx.get_toBoundCtx Γ j))
      rw [ih j]
      simp [Category.assoc]


theorem packedTypeIso_snoc (M : TypeModel τ V) (Γ : EffectCtx τ ε) (A : τ) (e : ε) :
    (M.productIso (packType Γ) A).inv ≫ (packedTypeIso M ((A, e) :: Γ)).hom =
      (packedTypeIso M Γ).hom ▷ M.obj A := by
  change (M.productIso (packType Γ) A).inv ≫
      ((M.productIso (packType Γ) A).hom ≫ ((packedTypeIso M Γ).hom ⊗ₘ 𝟙 (M.obj A))) = _
  simp

theorem packedTypeIso_pair (M : TypeModel τ V) (Γ : EffectCtx τ ε) (A B : τ) (e : ε) :
    Freyd.pairExtension M (packType Γ) A B ≫ (packedTypeIso M ((B,e) :: (A,e) :: Γ)).hom =
      ((packedTypeIso M Γ).hom ▷ M.obj (product A B)) ≫
        (boundObj M Γ.toBoundCtx ◁ (M.productIso A B).hom) ≫
          (α_ (boundObj M Γ.toBoundCtx) (M.obj A) (M.obj B)).inv := by
  unfold Freyd.pairExtension
  erw [Category.assoc, Category.assoc, Category.assoc, packedTypeIso_snoc M ((A, e) :: Γ) B e,
    ← MonoidalCategory.comp_whiskerRight, packedTypeIso_snoc M Γ A e,
    ← MonoidalCategory.associator_inv_naturality_left (packedTypeIso M Γ).hom (M.obj A) (M.obj B),
    MonoidalCategory.whisker_exchange_assoc]
  rfl


theorem packedEnvIso_lookup (M : TypeModel τ V) (Γ : EffectCtx τ ε) (i : Fin Γ.length) :
    (packedEnvIso M Γ).hom ≫ boundVar M (Γ := (Ctx.nil : Ctx Empty τ)) (β := Γ.toBoundCtx) i ≫
      eqToHom (congrArg M.obj (EffectCtx.get_toBoundCtx Γ i)) = Freyd.projection M Γ i := by
  rw [projection_transport]
  simp [packedEnvIso, boundVar, envObj, ctxObj, Category.assoc]

private theorem emptyEnv_snoc (M : TypeModel τ V) {n : Nat} (β : BoundCtx τ n) (A : τ) :
    ((λ_ (boundObj M β)).inv ▷ M.obj A) ≫
      (envSnocIso M (Ctx.nil : Ctx Empty τ) β A).hom =
      (λ_ (boundObj M (.snoc β A))).inv := by
  change ((λ_ (boundObj M β)).inv ▷ M.obj A) ≫
      (α_ (𝟙_ V) (boundObj M β) (M.obj A)).hom =
      (λ_ (boundObj M β ⊗ M.obj A)).inv
  simp

theorem packedEnvIso_snoc (M : TypeModel τ V) (Γ : EffectCtx τ ε) (A : τ) (e : ε) :
    (M.productIso (packType Γ) A).inv ≫ (packedEnvIso M ((A, e) :: Γ)).hom =
      ((packedEnvIso M Γ).hom ▷ M.obj A) ≫
        (envSnocIso M (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx A).hom := by
  let D := boundObj M Γ.toBoundCtx
  change (M.productIso (packType Γ) A).inv ≫
      ((packedTypeIso M ((A, e) :: Γ)).hom ≫ (λ_ (D ⊗ M.obj A)).inv) =
    (((packedTypeIso M Γ).hom ≫ (λ_ D).inv) ▷ M.obj A) ≫
      (envSnocIso M (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx A).hom
  erw [← Category.assoc, packedTypeIso_snoc M Γ A e, MonoidalCategory.comp_whiskerRight,
    Category.assoc, emptyEnv_snoc M Γ.toBoundCtx A]
  rfl

private theorem emptyEnv_pair (M : TypeModel τ V) {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    ((λ_ (boundObj M β)).inv ▷ (M.obj A ⊗ M.obj B)) ≫
      envPairHom M (Ctx.nil : Ctx Empty τ) β A B =
      (α_ (boundObj M β) (M.obj A) (M.obj B)).inv ≫
        (λ_ (boundObj M (.snoc (.snoc β A) B))).inv := by
  change _ ≫ ((α_ (𝟙_ V) (boundObj M β) (M.obj A ⊗ M.obj B)).hom ≫
        (𝟙_ V) ◁ (α_ (boundObj M β) (M.obj A) (M.obj B)).inv) = _
  monoidal_coherence

theorem packedEnvIso_pair (M : TypeModel τ V) (Γ : EffectCtx τ ε) (A B : τ) (e : ε) :
    Freyd.pairExtension M (packType Γ) A B ≫ (packedEnvIso M ((B, e) :: (A, e) :: Γ)).hom =
      ((packedEnvIso M Γ).hom ▷ M.obj (product A B)) ≫
        (envObj M (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx ◁ (M.productIso A B).hom) ≫
        envPairHom M (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx A B := by
  let D := boundObj M Γ.toBoundCtx
  change Freyd.pairExtension M (packType Γ) A B ≫
      ((packedTypeIso M ((B, e) :: (A, e) :: Γ)).hom ≫
        (λ_ ((D ⊗ M.obj A) ⊗ M.obj B)).inv) =
    (((packedTypeIso M Γ).hom ≫ (λ_ D).inv) ▷ M.obj (product A B)) ≫
      ((𝟙_ V ⊗ D) ◁ (M.productIso A B).hom) ≫
        envPairHom M (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx A B
  erw [← Category.assoc, packedTypeIso_pair M Γ A B e, MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  erw [← MonoidalCategory.whisker_exchange_assoc (λ_ D).inv (M.productIso A B).hom,
    emptyEnv_pair M Γ.toBoundCtx A B]
  erw [Category.assoc, Category.assoc]
  rfl

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Proofs

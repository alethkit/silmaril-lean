module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Transport

/-! # Transport between the chosen source Freyd operations and native denotation -/

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Semantics.Categorical (TypeModel InstructionModel boundObj boundLookup boundVar envSnocIso envPairHom envObj)

variable {τ : Type u} {Φ : Type v} {ε : Type w} [TypeFormers τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]

theorem projection_transport (M : TypeModel τ V) (Γ : EffectCtx τ ε) (i : Fin Γ.length) :
    Freyd.projection M Γ i =
      (packedTypeIso M Γ).hom ≫ boundLookup M (β := Γ.toBoundCtx) i ≫
        eqToHom (congrArg M.obj (EffectCtx.get_toBoundCtx Γ i)) :=
  Proofs.projection_transport M Γ i

theorem packedTypeIso_snoc (M : TypeModel τ V) (Γ : EffectCtx τ ε) (A : τ) (e : ε) :
    (M.productIso (packType Γ) A).inv ≫ (packedTypeIso M ((A, e) :: Γ)).hom =
      (packedTypeIso M Γ).hom ▷ M.obj A :=
  Proofs.packedTypeIso_snoc M Γ A e

theorem packedTypeIso_pair (M : TypeModel τ V) (Γ : EffectCtx τ ε) (A B : τ) (e : ε) :
    Freyd.pairExtension M (packType Γ) A B ≫ (packedTypeIso M ((B, e) :: (A, e) :: Γ)).hom =
      ((packedTypeIso M Γ).hom ▷ M.obj (product A B)) ≫
        (boundObj M Γ.toBoundCtx ◁ (M.productIso A B).hom) ≫
          (α_ (boundObj M Γ.toBoundCtx) (M.obj A) (M.obj B)).inv :=
  Proofs.packedTypeIso_pair M Γ A B e

theorem packedEnvIso_lookup (M : TypeModel τ V) (Γ : EffectCtx τ ε) (i : Fin Γ.length) :
    (packedEnvIso M Γ).hom ≫ boundVar M (Γ := (Ctx.nil : Ctx Empty τ)) (β := Γ.toBoundCtx) i ≫
      eqToHom (congrArg M.obj (EffectCtx.get_toBoundCtx Γ i)) = Freyd.projection M Γ i :=
  Proofs.packedEnvIso_lookup M Γ i

theorem packedEnvIso_snoc (M : TypeModel τ V) (Γ : EffectCtx τ ε) (A : τ) (e : ε) :
    (M.productIso (packType Γ) A).inv ≫ (packedEnvIso M ((A, e) :: Γ)).hom =
      ((packedEnvIso M Γ).hom ▷ M.obj A) ≫
        (envSnocIso M (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx A).hom :=
  Proofs.packedEnvIso_snoc M Γ A e

theorem packedEnvIso_pair (M : TypeModel τ V) (Γ : EffectCtx τ ε) (A B : τ) (e : ε) :
    Freyd.pairExtension M (packType Γ) A B ≫ (packedEnvIso M ((B, e) :: (A, e) :: Γ)).hom =
      ((packedEnvIso M Γ).hom ▷ M.obj (product A B)) ≫
        (envObj M (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx ◁ (M.productIso A B).hom) ≫
        envPairHom M (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx A B :=
  Proofs.packedEnvIso_pair M Γ A B e

section EffectTyping

variable [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : EffectCtx τ ε} {A : τ} {a : Expr Φ} {e : ε}

/-- A matched exact derivation also retains the source effect bound,
using the existing effect-typing correspondence. -/
theorem Lowering.hasTypeEffect
    (d : Lowering Γ a A) (ha : Wf Γ a A e) :
    LocallyNameless.HasTypeEffect (Ctx.nil : Ctx Empty τ) Γ.toBoundCtx d.term A e := by
  obtain ⟨_, lowered, typed⟩ := ha.toLetIter
  exact Option.some.inj (lowered.symm.trans d.lowered) ▸ typed

end EffectTyping

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C} {M : TypeModel τ V} [DistributiveFreydCategory J] [HasTy Φ τ] [InstructionModel J M Φ]
  [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {A : τ} {a : Expr Φ} {e : ε}
  {f : Arrow J M (packType Γ) A}

omit [HasEff Φ ε] [Preorder ε] [OrderBot ε] in
theorem Lowering.denote_eq_bound (d : Lowering Γ a A) :
    d.denote J M = J.map (packedTypeIso M Γ).hom ≫
      denoteBoundLoopFree J M d.typed (loopFree_of_lowering d.lowered) := by
  exact J.map_comp_assoc (packedTypeIso M Γ).hom (λ_ (boundObj M Γ.toBoundCtx)).inv
    (denoteLoopFree J M d.typed (loopFree_of_lowering d.lowered))

/-- A source Freyd derivation selects an exact native lowering derivation
whose transported loop-free denotation is the given arrow. -/
theorem exists_lowering (h : Denotes J M e Γ A a f) :
    ∃ d : Lowering Γ a A, d.denote J M = f :=
  Proofs.exists_lowering J M h

include J M in
theorem nonempty_lowering (h : Wf Γ a A e) : Nonempty (Lowering Γ a A) :=
  let ⟨_, hd⟩ := exists_denotes (J := J) (M := M) h
  let ⟨d, _⟩ := exists_lowering hd
  ⟨d⟩

/-- The image of a packed source class under a supplied comparison is
realized by a matched native loop-free derivation. -/
theorem exists_lowering_of_comparison (F : Comparison J M Φ e) (x : TypedExpr Φ Γ A e) :
    ∃ d : Lowering Γ x.val A, d.denote J M = F.map (pack (ofExpr x)) :=
  exists_lowering ((F.denotes_iff_map_pack x).mpr rfl)

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native

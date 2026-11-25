module

public import Silmaril.SSA.Isotope.Calco2019.LambdaSSA.Defs

/-! # The LambdaSSA CFG rule agrees with the CALCO loop -/

public section

universe u₁ u₂ u₃ u₄ v₁ v₂

namespace Silmaril.Isotope.Calco2019.LambdaSSA

open Silmaril.Calco2019
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Isotope.LetIter.ProofRelevant.Semantics.Categorical (contextualLoop caseWithContext)

section Freyd

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]

/-- The pure state changes of the Freyd model satisfy CALCO uniformity.
This also applies when the state includes a read-only CFG context. -/
theorem freyd_uniform : (categoricalFixpoints C).Uniform J :=
  (categorical_uniform_iff J).mpr (fun f g h comm => ElgotFreydCategory.pure_uniformity J f g h comm)

/-- Contextual loops solve the state enlarged by the read-only context and
then drop the context from the returned value. -/
theorem contextualLoop_eq {R A B : V}
    (body : J.obj (R ⊗ A) ⟶ J.obj (B ⨿ A)) :
    contextualLoop J body =
      (categoricalFixpoints C).iterate (contextualBody J body) trivial ≫
        J.map (CartesianMonoidalCategory.snd R B) := rfl

open Isotope.LambdaSSA
open Isotope.LambdaSSA.Semantics.Categorical
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- A nonempty typed CFG denotes the entry split followed either by an external
exit or by the CALCO solution of the local dispatcher. The collective arrow
is specified by its restrictions to the heterogeneous block arguments. -/
theorem cfg_denotes {n : Nat} {R : Fin (n + 1) → τ} {Γ : VCtx τ} {L : LCtx τ}
    {entry : Region Φ} {blocks : Fin (n + 1) → Region Φ}
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    {fe : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
    {fb : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj (labelObj M (List.ofFn R ++ L))}
    {collective : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶
      J.obj (labelObj M (List.ofFn R ++ L))}
    (de : RegionDenotes J M he fe)
    (db : ∀ i, RegionDenotes J M (hb i) (fb i))
    (dc : CollectiveDenotes J M Γ R L fb collective) :
    RegionDenotes J M (.cfg R he hb) (caseWithContext J
      (fe ≫ J.map (labelAppendSplit M (List.ofFn R) L))
      (J.map (CartesianMonoidalCategory.snd _ _))
      ((categoricalFixpoints C).iterate (contextualBody J
        (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelObjToFinite M R) ≫
          collective ≫ J.map (labelAppendSplit M (List.ofFn R) L))) trivial ≫
        J.map (CartesianMonoidalCategory.snd _ _))) :=
  .cfg he hb de db dc

end Freyd

section Kleisli

variable (m : Type u₁ → Type u₁) [Monad m] [LawfulMonad m]
  [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]

local notation "J" => Kleisli.Adjunction.toKleisli (ofTypeMonad m)

/-- In the instantiated Kleisli semantics, contextual CFG iteration is the
solution carried by the CALCO Elgot monad, including the coproduct comparison. -/
theorem contextualLoop_kleisli_eq {R A B : Type u₁}
    (body : (J).obj (R ⊗ A) ⟶ (J).obj (B ⨿ A)) :
    contextualLoop J body =
      (ofLawfulMonad m).iteration.iterate
        (contextualBody J body ≫
          (Kleisli.Type.coprodIsoSum m ((J).obj (R ⊗ B)) ((J).obj (R ⊗ A))).hom) trivial ≫
        (J).map (CartesianMonoidalCategory.snd R B) :=
  congrArg (· ≫ (J).map (CartesianMonoidalCategory.snd R B))
    (kleisli_iterate_eq m (contextualBody J body))

end Kleisli

end Silmaril.Isotope.Calco2019.LambdaSSA

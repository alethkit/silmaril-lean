module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Constructors.Normalization

/-! # Normalize mixed constructor returns under explicit sequencing equations
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.UnaryReturn Paper.RetainedLet
open Paper.TypeCategory Paper.BoundSimulation
open CategoryTheory CategoryTheory.Limits

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A B D : τ} {t c : Tm Φ}
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

omit [HasTy Φ τ] in
theorem Normalizes.pure {ε : Type w} [HasEff Φ ε] (pe : ε) (h : Normalizes Γ t c D) :
    Tm.Pure pe t :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Constructors.pure pe h

/-- Sequence the constructor arguments, then apply guarded β to each result. -/
theorem Normalizes.returnOnce_eq_branch (h : Normalizes Γ t c D)
    (includeFusion : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L)
    (seq : ConstructorSequencing Seed) :
    Paper.Extension.Eqv Seed Γ (returnOnce t) (.br 0 c) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Constructors.returnOnce_eq_branch h includeFusion seq

/-- A default commuting square at the constructor representative suffices,
even if the loop arrows are replaced by projected equivalents. -/
theorem Normalizes.iterate_map_uniformity (h : Normalizes [A] t c D)
    (includeFusion : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L)
    (seq : ConstructorSequencing Seed)
    {f f₀ : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A}
    {g g₀ : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType D}
    (hf : (Paper.Extension.Singleton.projection Seed).map f = (Paper.Extension.Singleton.projection Seed).map f₀)
    (hg : (Paper.Extension.Singleton.projection Seed).map g = (Paper.Extension.Singleton.projection Seed).map g₀)
    (comm : f₀ ≫ coprod.map (𝟙 (ofType B)) (ofRegion (.br (ℓ := 0) rfl h.typed.2)) =
      ofRegion (.br (ℓ := 0) rfl h.typed.2) ≫ g₀) :
    (Paper.Extension.Singleton.projection Seed).map (iterate f) =
      (Paper.Extension.Singleton.projection Seed).map (boundReturn h.typed.1) ≫
        (Paper.Extension.Singleton.projection Seed).map (iterate g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Constructors.iterate_map_uniformity h includeFusion seq hf hg comm

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors

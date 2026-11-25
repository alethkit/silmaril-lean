module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Normalization

/-! # Constructor uniformity for unary β normalizing state returns -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn

open CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory (returnRegion)
open Paper.TypeCategory
open BoundSimulation (boundReturn)
open RetainedLet (returnOnce returnOnce_typed)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A B D : τ} {t c : Tm Φ}
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

omit [HasTy Φ τ] in
/-- Unary β normalization uses constructor leaves, so no primitive effect is incurred. -/
theorem BetaNormalizes.pure {ε : Type w} [HasEff Φ ε] (pe : ε) (h : BetaNormalizes Γ t c D) :
    Tm.Pure pe t :=
  Beta.pure pe h

/-- Lowering a unary-let tree exposes its β reductions in the default region relation. -/
theorem BetaNormalizes.returnRegion_eq_branch (h : BetaNormalizes Γ t c D) :
    Paper.Eqv Γ (returnRegion t) (.br 0 c) [D] :=
  Beta.returnRegion_eq_branch h

/-- The only extra generator needed for the bind-first form is unary return fusion. -/
theorem BetaNormalizes.returnOnce_eq_branch (h : BetaNormalizes Γ t c D)
    (includeStep : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L) :
    Extension.Eqv Seed Γ (returnOnce t) (.br 0 c) [D] :=
  (returnRegion_eq_returnOnce includeStep h.hasType).symm.trans (.paper h.returnRegion_eq_branch)

/-- The bind-first state arrow has the indicated constructor representative after projection. -/
theorem BetaNormalizes.boundReturn_eq_constructor (h : BetaNormalizes [A] t c D)
    (includeStep : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L) :
    (Extension.Singleton.projection Seed).map (boundReturn h.hasType) =
      (Extension.Singleton.projection Seed).map (ofRegion (.br (ℓ := 0) rfl h.branchValue)) :=
  (Extension.Singleton.ofRegion_eq_iff Seed (returnOnce_typed h.hasType)
    (.br (ℓ := 0) rfl h.branchValue)).2 (h.returnOnce_eq_branch includeStep)

/-- A commuting square for the lowered return and chosen loop representatives
in the default category transports to the bind-first return in the extension. -/
theorem BetaNormalizes.iterate_map_uniformity (h : BetaNormalizes [A] t c D)
    (includeStep : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L)
    {f f₀ : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A}
    {g g₀ : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType D}
    (hf : (Extension.Singleton.projection Seed).map f = (Extension.Singleton.projection Seed).map f₀)
    (hg : (Extension.Singleton.projection Seed).map g = (Extension.Singleton.projection Seed).map g₀)
    (comm : f₀ ≫ coprod.map (𝟙 (ofType B)) (returnTerm h.hasType) = returnTerm h.hasType ≫ g₀) :
    (Extension.Singleton.projection Seed).map (iterate f) =
      (Extension.Singleton.projection Seed).map (boundReturn h.hasType) ≫
        (Extension.Singleton.projection Seed).map (iterate g) :=
  Beta.iterate_map_uniformity h includeStep hf hg comm

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn

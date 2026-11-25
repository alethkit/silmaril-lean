module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs

/-! # Guarded projection returns in a separate Paper presentation -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (returnRegion returnRegion_typed
  productFstBranches productSndBranches)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The first projection as an exactly typed expression. -/
theorem fstTerm (A B : τ) : Tm.HasType [product A B] (.let₂ (.var 0) (.var 1) : Tm Φ) A :=
  .let₂ (.var (i := 0) rfl) (.var (i := 1) rfl)

/-- The second projection as an exactly typed expression. -/
theorem sndTerm (A B : τ) : Tm.HasType [product A B] (.let₂ (.var 0) (.var 0) : Tm Φ) B :=
  .let₂ (.var (i := 0) rfl) (.var (i := 0) rfl)

/-- The two empty-capture projection instances of the companion's binary-let
return equation. The scrutinee is the sole input, the result is one of its two
components, and the exit interface is a singleton.

[Companion equation](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/Compose/Seq.lean#L314). -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | fst (A B : τ) : Step [product A B] (returnRegion (.let₂ (.var 0) (.var 1)))
      (.let₂ (.var 0) (.br 0 (.var 1))) [A]
  | snd (A B : τ) : Step [product A B] (returnRegion (.let₂ (.var 0) (.var 0)))
      (.let₂ (.var 0) (.br 0 (.var 0))) [B]

theorem Step.valueBranches {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ} (h : Step Γ r s L) :
    ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases h with
  | fst A B => exact ⟨returnRegion_typed (fstTerm A B), productFstBranches A B⟩
  | snd A B => exact ⟨returnRegion_typed (sndTerm A B), productSndBranches A B⟩

abbrev Eqv : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop :=
  Extension.Eqv Step

abbrev TypeCategory := Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ))

abbrev projection : Paper.TypeCategory (τ := τ) Φ ⥤ TypeCategory (τ := τ) (Φ := Φ) :=
  Extension.Singleton.projection Step

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns

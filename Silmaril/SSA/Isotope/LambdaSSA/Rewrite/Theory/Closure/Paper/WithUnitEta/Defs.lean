module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Defs

/-! # Guarded unit η in an opt-in Paper presentation -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The singleton instance of the companion's terminal rule on constructor
returns. The input variable and the literal unit both return immediately.

[Companion terminal rule](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Term/Step.lean#L18). -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | unit : Step [(Silmaril.unit : τ)] (.br 0 .unit) (.br 0 (.var 0)) [Silmaril.unit]

abbrev Eqv : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop :=
  Extension.Eqv Step

abbrev TypeCategory := Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ))

abbrev projection : Paper.TypeCategory (τ := τ) Φ ⥤ TypeCategory (τ := τ) (Φ := Φ) :=
  Extension.Singleton.projection Step

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithUnitEta

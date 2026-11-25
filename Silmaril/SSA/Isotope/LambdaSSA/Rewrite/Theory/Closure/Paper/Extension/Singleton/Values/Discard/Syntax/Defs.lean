module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Defs

/-! # Discard of a lowered singleton return -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (returnRegion)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "U" => (Silmaril.unit : τ)

/-- Returning a term and discarding its payload agrees with immediately returning unit. -/
def ReturnDiscards (Γ : VCtx τ) (a : Tm Φ) : Prop :=
  Eqv Seed Γ ((returnRegion a).lsubst (fun _ => .br 0 .unit)) (.br 0 .unit) [U]

/-- Erasing a marked primitive applied to the input variable in its singleton context. -/
def PrimitiveReturnsDiscard {ε : Type w} [HasEff Φ ε] (pe : ε) : Prop :=
  ∀ f : Φ, IsPure pe f →
    ReturnDiscards Seed [instrSrc f] (.op f (.var 0))

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension

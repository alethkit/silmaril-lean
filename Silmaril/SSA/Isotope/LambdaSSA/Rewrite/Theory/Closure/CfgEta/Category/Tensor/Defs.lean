module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Singleton.Defs

/-! # Computation whiskering in the one-block CFG η presentation

The Regions construction in §5.4 of *The Denotational Semantics of SSA*
(arXiv:2411.09347v2) uses the syntactic product on objects. Its two whiskerings
unpack the input, run the computation on one component, and return the result
paired with the retained component in the original order.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open Silmaril.DeBruijn (lift)

/-- The product type as an object of the empty-capture computation category. -/
def tensorObj {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    (X Y : TypeCategory Φ ([] : VCtx τ)) : TypeCategory Φ ([] : VCtx τ) :=
  ofType (Silmaril.product (show τ from X) (show τ from Y))

/-- The left-whiskering body receives the right component at index zero
and returns the left component (index two in the continuation) with the result. -/
def whiskerLeftBody {Φ : Type v} (r : Region Φ) : Region Φ :=
  (r.renameVars (lift (Nat.succ ∘ Nat.succ))).lsubst (fun _ => .br 0 (.pair (.var 2) (.var 0)))

/-- The right-whiskering body receives the left component at index one
and returns the result with the right component (index one in the continuation). -/
def whiskerRightBody {Φ : Type v} (r : Region Φ) : Region Φ :=
  (r.renameVars (Nat.succ ∘ lift Nat.succ)).lsubst (fun _ => .br 0 (.pair (.var 0) (.var 1)))

/-- Unpack the input pair and run the computation on its right component. -/
def whiskerLeftRegion {Φ : Type v} (r : Region Φ) : Region Φ :=
  .let₂ (.var 0) (whiskerLeftBody r)

/-- Unpack the input pair and run the computation on its left component. -/
def whiskerRightRegion {Φ : Type v} (r : Region Φ) : Region Φ :=
  .let₂ (.var 0) (whiskerRightBody r)

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

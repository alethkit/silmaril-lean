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

/-- For `X ⊗ f`, the right component is the computation input. The
return continuation uses index two for the retained left component. -/
def whiskerLeftRegion {Φ : Type v} (r : Region Φ) : Region Φ :=
  .let₂ (.var 0) ((r.renameVars (lift (Nat.succ ∘ Nat.succ))).lsubst
    (fun _ => .br 0 (.pair (.var 2) (.var 0))))

/-- For `f ⊗ X`, the left component is the computation input. The
return continuation uses index one for the retained right component. -/
def whiskerRightRegion {Φ : Type v} (r : Region Φ) : Region Φ :=
  .let₂ (.var 0) ((r.renameVars (Nat.succ ∘ lift Nat.succ)).lsubst
    (fun _ => .br 0 (.pair (.var 0) (.var 1))))

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

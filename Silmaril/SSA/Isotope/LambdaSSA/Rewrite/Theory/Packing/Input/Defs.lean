module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Defs

/-! # Packing an exact value context into a single input

The convention is the unit-terminated product in (86) and Appendix B.6 of
[The Denotational Semantics of SSA, arXiv:2411.09347v2](https://arxiv.org/abs/2411.09347v2).
In a newest-first list, the head type is the right factor.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

/-- The record type for a pure exact value context. -/
def packedInputType {τ : Type u} [TypeFormers τ] : VCtx τ → τ
  | [] => Silmaril.unit
  | A :: Γ => Silmaril.product (packedInputType Γ) A

/-- Assemble a record from the variables in their original context. -/
def packedInputValue {τ : Type u} {Φ : Type v} : VCtx τ → Tm Φ
  | [] => .unit
  | _ :: Γ => .pair ((packedInputValue Γ).rename Nat.succ) (.var 0)

/-- Read a variable from a record by traversing left factors and projecting right. -/
def packedInputProjection {Φ : Type v} : Nat → Tm Φ → Tm Φ
  | 0, a => .let₂ a (.var 0)
  | i + 1, a => packedInputProjection i (.let₂ a (.var 1))

/-- Replace free inputs by projections from the variable in the singleton context.
Substitution lifts past region binders, including local block arguments. -/
def packInputs {Φ : Type v} (r : Region Φ) : Region Φ :=
  r.substVars (fun i => packedInputProjection i (.var 0))

/-- Replace the singleton input with the record built from the original context. -/
def unpackInputs {τ : Type u} {Φ : Type v} (Γ : VCtx τ) (r : Region Φ) : Region Φ :=
  r.substVars (Tm.singleSubst (packedInputValue Γ))

end Silmaril.Isotope.LambdaSSA.Region

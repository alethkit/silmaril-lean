module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Defs

/-! # Packing a value context by destructuring its input record -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

namespace InputDestructure

/-- The context after splitting the record one field at a time. -/
def expanded : VCtx τ → VCtx τ → VCtx τ
  | [], Δ => Δ
  | A :: Γ, Δ => expanded Γ (A :: packedInputType Γ :: Δ)

/-- A pre-existing slot moves past two binders at every step. -/
def retained : VCtx τ → Nat → Nat
  | [], i => i
  | _ :: Γ, i => retained Γ (i + 2)

def field : VCtx τ → Nat → Nat
  | [], i => i
  | _ :: Γ, 0 => retained Γ 0
  | _ :: Γ, i + 1 => field Γ i

/-- Read the outer packet at `i`, then read the tail at variable one. -/
def split : VCtx τ → Nat → Region Φ → Region Φ
  | [], _, r => r
  | _ :: Γ, i, r => .let₂ (.var i) (split Γ 1 r)

end InputDestructure

/-- Pack the inputs by destructuring the record around the original CFG.
The body uses the original variables at their decoded slots. -/
def packInputsDestructure (r : Region Φ) (Γ : VCtx τ) : Region Φ :=
  InputDestructure.split Γ 0 (r.renameVars (InputDestructure.field Γ))

end Silmaril.Isotope.LambdaSSA.Region

module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat.Capture
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Region.InputDestructure

universe u w

variable {τ : Type u} {α : Type w}

/-- The environment after the decoder splits the given capture values. -/
def decoded : Nat → Env α → Env α → Env α
  | 0, _, ambient => ambient
  | n + 1, env, ambient =>
    decoded n (env ∘ Nat.succ) (extend (extend ambient (packEnv n (env ∘ Nat.succ))) (env 0))

private theorem decoded_retained (Γ : List τ) (original ambient : Env α) (i : Nat) :
    decoded Γ.length original ambient (retained Γ i) = ambient i := by
  induction Γ generalizing i original ambient with
  | nil => rfl
  | cons A Γ ih =>
    simp only [List.length_cons, retained, decoded, ih, LambdaSSA.Semantics.extend_succ]

theorem decoded_field (Γ : List τ) (original ambient : Env α) {i : Nat}
    (hi : i < Γ.length) : decoded Γ.length original ambient (field Γ i) = original i := by
  induction Γ generalizing i original ambient with
  | nil => simp at hi
  | cons A Γ ih =>
    cases i with
    | zero => simp only [List.length_cons, decoded, field, decoded_retained, LambdaSSA.Semantics.extend_zero]
    | succ i => exact ih _ _ (Nat.lt_of_succ_lt_succ hi)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture

module

public import Silmaril.Logic.Temporal.TLA.Defs

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Behavior

universe u

variable {S : Type u}

/-- Time `j` is the first later time with a different state from time `i`. -/
def FirstChange (σ : Behavior S) (i j : Nat) : Prop :=
  i < j ∧ σ j ≠ σ i ∧ ∀ k, i ≤ k → k < j → σ k = σ i

/-- The first later time with a different state, or `i` if the suffix is constant. -/
noncomputable def nextChange (σ : Behavior S) (i : Nat) : Nat :=
  open Classical in
  if h : ∃ j, σ.FirstChange i j then Classical.choose h else i

/-- The start time of the given constant block. After the final block starts,
the index stays at its start time. -/
noncomputable def blockStart (σ : Behavior S) : Nat → Nat
  | 0 => 0
  | n + 1 => σ.nextChange (σ.blockStart n)

/-- Lamport's canonical stutter reduction `#σ` (§8.2, equation 48). Each finite
constant block contributes one state and an infinite final block contributes
a constant tail. -/
noncomputable def canonicalReduction (σ : Behavior S) : Behavior S :=
  fun n => σ (σ.blockStart n)

/-- The three clauses of equation (48), with stream concatenation written as
a head at zero followed by the reduced suffix. -/
def SatisfiesLamport48 (reduce : Behavior S → Behavior S) : Prop :=
  ∀ σ,
    ((∀ i, σ i = σ 0) → reduce σ = fun _ => σ 0) ∧
    ((∃ i, σ i ≠ σ 0) → σ 1 = σ 0 → reduce σ = reduce (σ.suffix 1)) ∧
    (σ 1 ≠ σ 0 → reduce σ = fun
      | 0 => σ 0
      | n + 1 => reduce (σ.suffix 1) n)

end Silmaril.Logic.Temporal.TLA.Behavior

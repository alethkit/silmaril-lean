module

public import Silmaril.Semantics.SOS.Defs

@[expose] public section

namespace Silmaril.Semantics.SOS.Proofs

universe u

theorem immediate_iff {J : Type u} {R : Set (Rule J)} {j : J} :
    immediate R (Derives R) j ↔ Derives R j := by
  constructor
  · rintro ⟨r, hr, rfl, premises⟩
    exact .apply hr premises
  · intro h
    cases h with
    | apply hr premises => exact ⟨_, hr, rfl, premises⟩

end Silmaril.Semantics.SOS.Proofs

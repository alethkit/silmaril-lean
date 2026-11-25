module

public import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Proofs

theorem run_iff {C : Type} {site : Site} (render : State → C) (native : C → C → Prop)
    (one : ∀ {a dst}, Admitted site a → (native (render a) dst ↔ ∃ b, Edge site a b ∧ dst = render b))
    {a : State} {dst : C} (ready : Admitted site a) :
    Relation.ReflTransGen native (render a) dst ↔
      ∃ b, Runs site a b ∧ Admitted site b ∧ dst = render b := by
  constructor
  · intro run
    induction run with
    | refl => exact ⟨_, .refl, ready, rfl⟩
    | tail _ step ih =>
      obtain ⟨_, trace, ok, rfl⟩ := ih
      obtain ⟨_, edge, rfl⟩ := (one ok).mp step
      exact ⟨_, trace.tail edge, Indexed.closed ok edge, rfl⟩
  · rintro ⟨b, run, admitted, rfl⟩
    clear admitted
    have trace : Relation.ReflTransGen native (render a) (render b) ∧ Admitted site b := by
      induction run with
      | refl => exact ⟨.refl, ready⟩
      | tail _ edge ih => exact ⟨ih.1.tail ((one ih.2).mpr ⟨_, edge, rfl⟩), Indexed.closed ih.2 edge⟩
    exact trace.1

end Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Proofs

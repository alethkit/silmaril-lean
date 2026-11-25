module

public import Silmaril.Wasm.Institution.Operational.Blocks.Context.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Context.Proofs

open Execution.Runtime (Value)

theorem typed_step {A : Type} {results : List NumType} {a b : Returning A}
    (typed : a.Typed results) (step : ReturnStep a b) : b.Typed results := by
  induction step with
  | exit scope stack rest =>
    change (stack.map Value.type).reverse.take results.length = results.reverse at typed
    have enough : results.length ≤ (stack.map Value.type).reverse.length := by
      have length := congrArg List.length typed
      simp only [List.length_take, List.length_reverse, List.length_map] at length
      simp only [List.length_reverse, List.length_map]
      omega
    simpa only [Returning.Typed, List.map_append, List.reverse_append, List.take_append_of_le_length enough] using typed
  | under scope step ih => exact ih typed

theorem run_iff {A C : Type} (render : Returning A → C) (step : C → C → Prop)
    (one : ∀ {a b}, step (render a) b ↔ ∃ out, ReturnStep a out ∧ b = render out)
    {a : Returning A} {b : C} :
    Relation.ReflTransGen step (render a) b ↔ ∃ out, ReturnRuns a out ∧ b = render out := by
  constructor
  · intro trace
    induction trace with
    | refl => exact ⟨a, .refl, rfl⟩
    | tail _ h ih =>
      obtain ⟨_, run, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := one.mp h
      exact ⟨out, run.tail edge, rfl⟩
  · rintro ⟨out, run, rfl⟩
    induction run with
    | refl => exact .refl
    | tail _ h ih => exact ih.tail (one.mpr ⟨_, h, rfl⟩)

end Silmaril.Wasm.Institution.Operational.Blocks.Context.Proofs

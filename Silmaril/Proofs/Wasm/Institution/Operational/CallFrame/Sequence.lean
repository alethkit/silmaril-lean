module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallFrame.Proofs

/-- The one non-value at the end of a sequence belongs to the stepping middle.
The prefix removed by the instruction context consists of whole values. -/
theorem split_context {V A : Type} (emit : V → A) (read : A → Option V)
    (roundtrip : ∀ v, read (emit v) = some v) (saved stack : List V) {mid tail : List A}
    {op : A} (active : ∃ a ∈ mid, read a = none)
    (eq : saved.map emit ++ mid ++ tail = stack.map emit ++ [op]) :
    ∃ args, stack = saved ++ args ∧ mid = args.map emit ++ [op] ∧ tail = [] := by
  induction saved generalizing stack with
  | nil =>
    change mid ++ tail = stack.map emit ++ [op] at eq
    obtain ⟨a, ha, noValue⟩ := active
    have noPrefix (bad : a ∈ stack.map emit) : False := by
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp bad
      rw [roundtrip] at noValue
      contradiction
    rcases List.append_eq_append_iff.mp eq with ⟨tail', frontEq, suffix⟩ | ⟨front, frontEq, suffix⟩
    · exact (noPrefix (frontEq ▸ List.mem_append_left tail' ha)).elim
    · rcases List.singleton_eq_append_iff.mp suffix with ⟨rfl, tailEq⟩ | ⟨rfl, rfl⟩
      · exact (noPrefix (by simpa [frontEq] using ha)).elim
      · exact ⟨stack, rfl, frontEq, rfl⟩
  | cons v saved ih =>
    cases stack with
    | nil =>
      have len := congrArg List.length eq
      obtain ⟨a, member, _⟩ := active
      have pos := List.length_pos_iff.mpr (List.ne_nil_of_mem member)
      change ((v :: saved).map emit ++ mid ++ tail).length = 1 at len
      simp only [List.length_append, List.length_map, List.length_cons] at len
      omega
    | cons w stack =>
      have split := List.cons.inj eq
      have same : v = w := by
        have check := congrArg read split.1
        simpa only [roundtrip, Option.some.injEq] using check
      subst w
      obtain ⟨args, rfl, rfl, rfl⟩ := ih stack split.2
      exact ⟨args, rfl, rfl, rfl⟩

theorem stack_injective {V A : Type} (emit : V → A) (read : A → Option V)
    (roundtrip : ∀ v, read (emit v) = some v) :
    Function.Injective (fun vs : List V => vs.map emit) := by
  intro xs ys eq
  have back := congrArg (List.filterMap read) eq
  simpa [List.filterMap_map, roundtrip] using back

theorem returned_suffix {V : Type} {a b x y : List V}
    (eq : a ++ b = x ++ y) (length : b.length = y.length) :
    a = x ∧ b = y := by
  have fronts := congrArg List.length eq
  simp only [List.length_append, length] at fronts
  exact List.append_inj eq (by omega)

end Silmaril.Wasm.Institution.Operational.CallFrame.Proofs

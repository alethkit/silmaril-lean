module

public import Silmaril.Logic.Temporal.TLA.Data.Defs
import Silmaril.Proofs.Logic.Temporal.TLA.Data.Sets

public section

namespace Silmaril.Logic.Temporal.TLA.Data

universe u

variable {V : Type u}

namespace ChoicePolicy

variable (policy : ChoicePolicy V) {p q : V → Prop}

/-- The two sides of the witness rule (16.2) for proposition-valued predicates. -/
theorem exists_iff_choose : (∃ x, p x) ↔ p (policy.choose p) :=
  ⟨policy.witness, fun h => ⟨_, h⟩⟩

/-- Choice depends on the predicate's extension. -/
theorem congr (h : ∀ x, p x ↔ q x) : policy.choose p = policy.choose q :=
  congrArg policy.choose (funext fun x => propext (h x))

theorem choose_of_no_witness (h : ¬ ∃ x, p x) : policy.choose p = policy.noWitness :=
  policy.congr (fun x => iff_of_false (fun hx => h ⟨x, hx⟩) id)

@[simp] theorem classical_noWitness (fallback : V) :
    (ChoicePolicy.classical fallback).noWitness = fallback := by
  classical
  simp [noWitness, ChoicePolicy.classical]

end ChoicePolicy

namespace Model

variable (M : Model V) {s t x : V} {p q : V → Prop}

theorem ext_iff : s = t ↔ ∀ x, M.mem x s ↔ M.mem x t :=
  ⟨fun h => h ▸ fun _ => Iff.rfl, M.ext⟩

@[simp] theorem mem_enum (values : List V) :
    M.mem x (M.enum values) ↔ x ∈ values :=
  Proofs.Logic.Temporal.TLA.Data.mem_enum M x values

@[simp] theorem mem_union : M.mem x (M.union s t) ↔ M.mem x s ∨ M.mem x t := by
  simp [union, M.mem_sUnion, M.mem_enum, or_and_right, exists_or]

@[simp] theorem mem_inter : M.mem x (M.inter s t) ↔ M.mem x s ∧ M.mem x t :=
  M.mem_sep

@[simp] theorem mem_diff : M.mem x (M.diff s t) ↔ M.mem x s ∧ ¬ M.mem x t :=
  M.mem_sep

theorem mem_powerset_iff_subset : M.mem t (M.powerset s) ↔ M.subset t s :=
  M.mem_powerset

theorem empty_ne_singleton : M.empty ≠ M.insert M.empty M.empty := by
  have hm : M.mem M.empty (M.insert M.empty M.empty) := M.mem_insert.mpr (.inl rfl)
  exact fun h => M.notMem_empty M.empty ((congrArg (M.mem M.empty) h).mpr hm)

/-- Separation rules out a set containing every value. -/
theorem not_universal (s : V) : ¬ ∀ x, M.mem x s :=
  Proofs.Logic.Temporal.TLA.Data.not_universal M s

/-- Every set has a value outside it in the same carrier. -/
theorem exists_not_mem (s : V) : M.existsValue (fun x => ¬ M.mem x s) :=
  Classical.not_forall.mp (M.not_universal s)

@[simp] theorem not_existsIn_empty : ¬ M.existsIn M.empty p :=
  fun ⟨x, hx, _⟩ => M.notMem_empty x hx

@[simp] theorem forallIn_empty : M.forallIn M.empty p :=
  fun x hx => (M.notMem_empty x hx).elim

theorem existsValue_iff_choose : M.existsValue p ↔ p (M.choose p) :=
  M.choice.exists_iff_choose

theorem choose_congr (h : ∀ x, p x ↔ q x) : M.choose p = M.choose q :=
  M.choice.congr h

theorem choose_of_no_witness (h : ¬ M.existsValue p) : M.choose p = M.choice.noWitness :=
  M.choice.choose_of_no_witness h

theorem existsIn_iff_chooseIn :
    M.existsIn s p ↔ M.mem (M.chooseIn s p) s ∧ p (M.chooseIn s p) :=
  M.existsValue_iff_choose

theorem chooseIn_congr (h : ∀ x, M.mem x s → (p x ↔ q x)) :
    M.chooseIn s p = M.chooseIn s q :=
  M.choose_congr fun x => and_congr_right (h x)

theorem chooseIn_of_no_witness (h : ¬ M.existsIn s p) :
    M.chooseIn s p = M.choice.noWitness :=
  M.choose_of_no_witness h

end Model
end Silmaril.Logic.Temporal.TLA.Data

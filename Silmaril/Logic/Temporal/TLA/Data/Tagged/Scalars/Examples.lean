module

import Silmaril.Logic.Temporal.TLA.Data.Tagged.Scalars.Thms

/-! Checked numeric and mixed-set examples for the evaluator handoff. -/

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

private def unspecified : Unspecified.{0} := fun _ _ => .boolean false

example : (SetData.naturals : SetData.{0}).mem (.integer 12) :=
  (SetData.integer_mem_naturals 12).mpr (by decide)

example : ¬ (SetData.naturals : SetData.{0}).mem (.integer (-1)) := by
  rw [SetData.integer_mem_naturals]
  decide

example (n : Int) : (SetData.integers : SetData.{0}).mem (.integer n) :=
  SetData.mem_integers.mpr ⟨n, rfl⟩

example : (Value.integer 12).mem (Value.interval unspecified (.integer 1) (.integer 12)) := by
  simp [SetData.integer_mem_intRange]

example (n : Int) : ¬ (Value.integer n).mem (Value.interval unspecified (.integer 5) (.integer 4)) := by
  simp [SetData.integer_mem_intRange]
  omega

example : Value.add unspecified (.integer 11) (.integer 1) = .integer 12 :=
  Value.add_integer unspecified 11 1

example : Value.modulo unspecified (.integer 12) (.integer 12) = .integer 0 :=
  Value.modulo_integer unspecified 12 12 (by decide)

example : Value.add unspecified (.boolean true) (.integer 4) = .boolean false :=
  Value.add_bad_left unspecified (Value.asInt_boolean true)

example : (Value.integer 0).mem (.set (SetData.enum
    [Value.boolean.{0} true, .integer 0, .set SetData.empty])) := by
  simp

example (s : SetData.{0}) : ¬ s.powerset.mem (.boolean true) :=
  fun h => let ⟨t, ht, _⟩ := SetData.mem_powerset.mp h; Value.boolean_ne_set true t ht.symm

end Silmaril.Logic.Temporal.TLA.Data.Tagged

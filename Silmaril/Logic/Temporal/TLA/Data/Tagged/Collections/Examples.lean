module

import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Thms

/-! Examples connecting unbounded graphs, updates and derived function values. -/

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

private def unspecified : Unspecified.{0} := fun _ _ => .boolean false

private noncomputable def integerIdentity : Graph.{0} :=
  Graph.ofFn SetData.integers id

example : (SetData.integers.functionSet SetData.integers).mem (Value.function integerIdentity) := by
  apply SetData.mem_functionSet.mpr
  refine ⟨integerIdentity, rfl, Graph.domain_ofFn _ _, ?_⟩
  intro x y h
  have hxy := Graph.relates_ofFn.mp h
  exact hxy.2 ▸ hxy.1

example (n : Int) :
    Value.apply unspecified (Value.function integerIdentity) (.integer n) = .integer n :=
  Value.apply_function unspecified (Graph.relates_ofFn.mpr ⟨SetData.mem_integers.mpr ⟨n, rfl⟩, rfl⟩)

private theorem boolean_not_in_domain : ¬ integerIdentity.domain.mem (.boolean true) := by
  rw [integerIdentity, Graph.domain_ofFn, SetData.mem_integers]
  exact fun ⟨n, h⟩ => Value.integer_ne_boolean n true h

example : Value.apply unspecified (Value.function integerIdentity) (.boolean true) = .boolean false :=
  Value.apply_missing unspecified boolean_not_in_domain

example : Value.update unspecified (Value.function integerIdentity) (.boolean true) (.integer 7) =
    Value.function integerIdentity :=
  Value.update_missing unspecified boolean_not_in_domain

example : Value.update unspecified (.boolean true) (.integer 0) (.integer 7) = .boolean false :=
  Value.update_nonfunction unspecified (Value.asFunction_boolean true)

example (g : Graph.{0}) (x : Value.{0}) (h : g.domain.mem x) :
    Value.apply unspecified (Value.update unspecified (.function g) x (.integer 7)) x = .integer 7 := by
  rw [Value.update_function]
  exact Value.apply_function unspecified (Graph.lookup_eq_some.mp (Graph.lookup_update h))

example : Value.string.{0} "" = Value.tuple [] :=
  Value.string_empty

example : Value.apply unspecified (Value.record ["hour"] (fun _ => .integer 12)) (.string "hour") =
    .integer 12 :=
  Value.apply_function unspecified (Graph.lookup_eq_some.mp (Graph.lookup_record _ (by simp)))

end Silmaril.Logic.Temporal.TLA.Data.Tagged

module

import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.Thms
import Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Thms

/-! # Reference-style regressions for path and clause evaluation -/

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

private def policy : Unspecified.{0}
  | .apply, _ => Value.integer 0
  | .update, [_, _, result] => result
  | _, _ => Value.boolean false

private noncomputable def cells : Graph.{0} :=
  Graph.ofFn (SetData.intRange 1 2) fun _ => Value.integer 10

private noncomputable def recordBody (field : String) : Value.{0} :=
  if field = "cells" then Value.function cells else Value.boolean true

private noncomputable def recordGraph : Graph.{0} :=
  Graph.record ["cells", "ready"] recordBody

private noncomputable def root : Value.{0} := Value.function recordGraph

private noncomputable def cellPath : List Value.{0} := [Value.string "cells", Value.integer 1]

private noncomputable def bump : ExceptClause.{0} :=
  ⟨cellPath, fun old => old.add policy (Value.integer 1)⟩

private theorem lookup_cells :
    recordGraph.lookup (Value.string "cells") = some (Value.function cells) := by
  change (Graph.record ["cells", "ready"] recordBody).lookup (Value.string "cells") = _
  rw [Graph.lookup_record recordBody (by simp)]
  rfl

private theorem first_cell : root.lookupPath cellPath = .found (Value.integer 10) := by
  change (Value.function recordGraph).lookupPath [Value.string "cells", Value.integer 1] = _
  rw [Value.lookupPath_through_key lookup_cells]
  have h : (SetData.intRange 1 2).mem (Value.integer.{0} 1) :=
    (SetData.integer_mem_intRange 1 2 1).mpr (by decide)
  have hc : cells.lookup (Value.integer 1) = some (Value.integer 10) :=
    Graph.lookup_ofFn (f := fun _ => Value.integer.{0} 10) h
  rw [Value.lookupPath_through_key hc, Value.lookupPath_nil]

/-- `[r EXCEPT !.cells[1] = @ + 1, !.cells[1] = @ + 1]` reads 10 and then 11. -/
example : (root.updateClauses policy [bump, bump]).lookupPath cellPath =
    .found (Value.integer 12) := by
  have once := Value.lookupPath_update_found policy (replacement := bump.replacement) first_cell
  have twice := Value.lookupPath_update_found policy (replacement := bump.replacement) once
  simpa [bump, Value.updateClauses] using twice

/-- Updating a nested cell preserves the sibling field. -/
example : (root.updatePath policy cellPath bump.replacement).lookupPath [Value.string "ready"] =
    .found (Value.boolean true) := by
  have hne : Value.string.{0} "ready" ≠ Value.string "cells" :=
    fun h => (by decide : "ready" ≠ "cells") (Value.string_injective h)
  change ((Value.function recordGraph).updatePath policy
    (Value.string "cells" :: [Value.integer 1]) bump.replacement).lookupPath
      (Value.string "ready" :: []) = _
  rw [Value.lookupPath_update_sibling policy hne]
  have hr : recordGraph.lookup (Value.string "ready") = some (Value.boolean true) := by
    change (Graph.record ["cells", "ready"] recordBody).lookup (Value.string "ready") = _
    rw [Graph.lookup_record recordBody (by simp)]
    rfl
  rw [Value.lookupPath_through_key hr, Value.lookupPath_nil]

/-- A missing inner key preserves the entire record, including its outer domain. -/
example : root.updatePath policy [Value.string "cells", Value.integer 3] bump.replacement = root := by
  apply Value.updatePath_missing
  change (Value.function recordGraph).lookupPath [Value.string "cells", Value.integer 3] = _
  rw [Value.lookupPath_through_key lookup_cells]
  apply Value.lookupPath_missing_key
  change ¬ (Graph.ofFn (SetData.intRange 1 2) (fun _ => Value.integer.{0} 10)).domain.mem (Value.integer 3)
  rw [Graph.domain_ofFn, SetData.integer_mem_intRange]
  decide

/-- A non-function uses the fixed application and update policy, even for a singleton path. -/
example : (Value.boolean true).updatePath policy [Value.integer 1] bump.replacement =
    Value.integer 1 := by
  rw [Value.updatePath_nonfunction policy (Value.asFunction_boolean true)]
  simp [policy, bump]

end Silmaril.Logic.Temporal.TLA.Data.Tagged

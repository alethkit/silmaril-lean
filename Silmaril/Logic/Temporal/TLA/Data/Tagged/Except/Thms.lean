module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Functions.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.Data.Tagged.Except

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged.Value

universe u

variable (policy : Unspecified.{u}) {root key child sibling old : Value.{u}} {g : Graph.{u}}
  {path tail : List Value.{u}} {replacement : Value.{u} → Value.{u}}

@[simp] theorem lookupPath_nil (root : Value.{u}) : root.lookupPath [] = .found root := rfl

@[simp] theorem lookupPath_through_key (h : g.lookup key = some child) :
    (function g).lookupPath (key :: path) = child.lookupPath path := by
  simp only [lookupPath, asFunction_function, h]

theorem lookupPath_missing_key (h : ¬ g.domain.mem key) :
    (function g).lookupPath (key :: path) = .missingKey := by
  simp only [lookupPath, asFunction_function, Graph.lookup_eq_none.mpr h]

theorem lookupPath_nonfunction (h : root.asFunction = none) :
    root.lookupPath (key :: path) = .nonFunction := by
  rw [lookupPath, h]

@[simp] theorem updatePath_nil : updatePath policy root [] replacement = replacement root := rfl

/-- A singleton path uses exactly the existing application and update policy. -/
theorem updatePath_single :
    updatePath policy root [key] replacement =
      update policy root key (replacement (apply policy root key)) := rfl

theorem updatePath_through_key (h : g.lookup key = some child) :
    updatePath policy (function g) (key :: path) replacement =
      function (g.update key (updatePath policy child path replacement)) :=
  Proofs.updatePath_through_key policy h

/-- The same path is valid after the update and selects the replacement of the old leaf. -/
theorem lookupPath_update_found (h : root.lookupPath path = .found old) :
    (updatePath policy root path replacement).lookupPath path = .found (replacement old) :=
  Proofs.lookupPath_update_found policy h

/-- A missing key anywhere along a path through recognized functions leaves the root unchanged. -/
theorem updatePath_missing (h : root.lookupPath path = .missingKey) :
    updatePath policy root path replacement = root :=
  Proofs.updatePath_missing policy h

theorem updatePath_nonfunction (h : root.asFunction = none) :
    updatePath policy root (key :: path) replacement =
      policy .update [root, key, updatePath policy (policy .apply [root, key]) path replacement] := by
  rw [updatePath, apply_nonfunction policy h, update_nonfunction policy h]

/-- The domain of an updated parent is the domain before rebuilding it. -/
theorem domain_updatePath_function :
    domain policy (updatePath policy (function g) (key :: path) replacement) = set g.domain := by
  simp only [updatePath, update_function, domain_function, Graph.domain_update]

/-- A path through a different key of the same parent still yields the same result. -/
theorem lookupPath_update_sibling (hne : sibling ≠ key) :
    (updatePath policy (function g) (key :: path) replacement).lookupPath (sibling :: tail) =
      (function g).lookupPath (sibling :: tail) := by
  simp only [updatePath, update_function, lookupPath, asFunction_function, Graph.lookup_update_other hne]

@[simp] theorem updateClauses_nil : updateClauses policy root [] = root := rfl

theorem updateClauses_cons (clause : ExceptClause.{u}) (clauses : List ExceptClause.{u}) :
    updateClauses policy root (clause :: clauses) =
      updateClauses policy (updatePath policy root clause.path clause.replacement) clauses := rfl

theorem updateClauses_append (first later : List ExceptClause.{u}) :
    updateClauses policy root (first ++ later) =
      updateClauses policy (updateClauses policy root first) later :=
  List.foldl_append

end Silmaril.Logic.Temporal.TLA.Data.Tagged.Value

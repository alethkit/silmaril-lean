module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Functions.Thms

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged.Proofs

universe u

open Value

variable {g : Graph.{u}} {root key child old : Value.{u}} {path : List Value.{u}}
  {replacement : Value.{u} → Value.{u}} (policy : Unspecified.{u})

theorem updatePath_through_key (h : g.lookup key = some child) :
    updatePath policy (function g) (key :: path) replacement =
      function (g.update key (updatePath policy child path replacement)) := by
  rw [updatePath, apply_function policy (Graph.lookup_eq_some.mp h), update_function]

private theorem graph_update_old (h : g.lookup key = some child) : g.update key child = g := by
  classical
  have hm : g.domain.mem key := Graph.mem_domain.mpr ⟨child, Graph.lookup_eq_some.mp h⟩
  apply Graph.ext
  intro k
  by_cases hk : k = key
  · subst k
    rw [Graph.lookup_update hm, h]
  · exact Graph.lookup_update_other hk

theorem lookupPath_update_found (h : root.lookupPath path = .found old) :
    (updatePath policy root path replacement).lookupPath path = .found (replacement old) := by
  induction path generalizing root with
  | nil =>
    have he : root = old := PathLookup.found.inj h
    subst root
    rfl
  | cons key path ih =>
    cases hg : root.asFunction with
    | none => simp [lookupPath, hg] at h
    | some g =>
      have he := Value.asFunction_eq_some.mp hg
      subst root
      cases hk : g.lookup key with
      | none => simp [lookupPath, hk] at h
      | some child =>
        have htail : child.lookupPath path = .found old := by
          simpa only [lookupPath, asFunction_function, hk] using h
        have hm : g.domain.mem key := Graph.mem_domain.mpr ⟨child, Graph.lookup_eq_some.mp hk⟩
        simpa only [updatePath_through_key policy hk, lookupPath, asFunction_function,
          Graph.lookup_update hm] using ih htail

theorem updatePath_missing (h : root.lookupPath path = .missingKey) :
    updatePath policy root path replacement = root := by
  induction path generalizing root with
  | nil => cases h
  | cons key path ih =>
    cases hg : root.asFunction with
    | none => simp [lookupPath, hg] at h
    | some g =>
      have he := Value.asFunction_eq_some.mp hg
      subst root
      cases hk : g.lookup key with
      | none =>
        rw [updatePath]
        exact update_missing policy (Graph.lookup_eq_none.mp hk)
      | some child =>
        have htail : child.lookupPath path = .missingKey := by
          simpa only [lookupPath, asFunction_function, hk] using h
        rw [updatePath_through_key policy hk, ih htail, graph_update_old hk]

end Silmaril.Logic.Temporal.TLA.Data.Tagged.Proofs

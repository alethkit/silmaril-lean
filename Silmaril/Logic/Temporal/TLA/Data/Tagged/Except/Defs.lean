module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Functions.Defs

/-! # Mathematical EXCEPT paths

Keys and right-hand sides are already denoted. Each right-hand side takes
the value of the old leaf bound by its own clause.
-/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

/-- Result of following a path using only recognized functions and in-domain keys. -/
inductive PathLookup where
  | found (leaf : Value.{u})
  | missingKey
  | nonFunction

/-- A clause whose path components are value keys. The source requires a nonempty path. -/
structure ExceptClause where
  path : List Value.{u}
  replacement : Value.{u} → Value.{u}

namespace Value

/-- Inspect a path without consulting the policy for unspecified operations. -/
noncomputable def lookupPath (root : Value.{u}) (path : List Value.{u}) : PathLookup.{u} :=
  match path with
  | [] => .found root
  | key :: rest =>
    match root.asFunction with
    | none => .nonFunction
    | some g =>
      match g.lookup key with
      | none => .missingKey
      | some child => child.lookupPath rest
termination_by structural path

/-- Rebuild a path from its old leaf using the same single-key operations at each parent.
The empty path replaces the root and serves as the recursion base. -/
noncomputable def updatePath (policy : Unspecified.{u}) (root : Value.{u})
    (path : List Value.{u}) (replacement : Value.{u} → Value.{u}) : Value.{u} :=
  match path with
  | [] => replacement root
  | key :: rest =>
    update policy root key (updatePath policy (apply policy root key) rest replacement)
termination_by structural path

/-- Evaluate clauses in order, using the preceding result as the next clause's root. -/
noncomputable def updateClauses (policy : Unspecified.{u}) (root : Value.{u})
    (clauses : List ExceptClause.{u}) : Value.{u} :=
  clauses.foldl (fun current clause => updatePath policy current clause.path clause.replacement) root

end Value
end Silmaril.Logic.Temporal.TLA.Data.Tagged

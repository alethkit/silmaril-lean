module

import Silmaril.Languages.Starlark.Modules.Loader.Thms
meta import Silmaril.Languages.Starlark.Modules.Loader.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs
meta import Silmaril.Languages.Starlark.Lists.Freeze.Defs

namespace Silmaril.Languages.Starlark.Modules.Loader

open Lists (State)

private def global (name : String) : Lists.Expr := .read (.bound (globalSlot name))
private def localRef (name : String) : Lists.Expr := .read (.bound (fileSlot name))
private def int (n : Int) : Lists.Expr := .scalar (.int n)
private def set (name : String) (value : Lists.Expr) : Command :=
  .exec (.atomic (.assign (globalSlot name) value))
private def effect (value : Lists.Expr) : Command := .exec (.atomic (.eval value))
private def imp (label exportName alias : String) : Command := .load label [⟨exportName, alias⟩]

private def leaf : Entry := ⟨⟨["out"], [], [set "out" (.list .empty)]⟩, []⟩

private def diamond : Manifest := #[
  ⟨⟨["out"], [], [imp "route" "out" "left", imp "right" "out" "right",
    imp "again" "out" "again", set "out" (.tuple (.cons (localRef "left")
      (.cons (localRef "right") (.cons (localRef "again") .empty))))]⟩,
    [("route", 1), ("right", 2), ("again", 3)]⟩,
  ⟨⟨["out"], [], [imp "route" "out" "leaf", set "out" (localRef "leaf")]⟩, [("route", 3)]⟩,
  ⟨⟨["out"], [], [imp "leaf" "out" "leaf", set "out" (localRef "leaf")]⟩, [("leaf", 3)]⟩,
  leaf]

-- Publication preserves the shared leaf and a later entry in the same session is a cache hit.
#guard
  let caller : State := { iterators := [22] }
  match load #[] diamond 0 { runtime := caller } with
  | .ok published session =>
    match published.exports, load #[] diamond 0 session with
    | [("out", .tuple root)], .ok _ reused =>
      match Lists.tupleElements root session.runtime with
      | .ok [.list a, .list b, .list c] _ =>
        a == b && b == c && (session.cache.map Prod.fst) == [0, 2, 1, 3] &&
          session.runtime.iterators == [22] && reused.runtime.heap == session.runtime.heap &&
          (session.runtime.heap[a]?.map Lists.Cell.frozen) == some true
      | _ => false
    | _, _ => false
  | .error _ _ => false

private def cyclic : Manifest := #[
  ⟨⟨["out"], [], [set "out" (.list .empty), imp "next" "out" "dep"]⟩, [("next", 1)]⟩,
  ⟨⟨["out"], [], [set "out" (.list .empty), imp "next" "out" "dep"]⟩, [("next", 0)]⟩]

private def lists (session : Session) : List (List Lists.Value × Bool) :=
  session.runtime.heap.toList.filterMap fun
    | ⟨.list values, frozen⟩ => some (values, frozen)
    | _ => none

#guard
  match load #[] cyclic 0 with
  | .error (.cycle [0, 1, 0]) session => session.cache.isEmpty &&
      decide (lists session = [([], false), ([], false)]) &&
      (session.runtime.slots (globalSlot "out")).isNone
  | _ => false

private def failing : Manifest := #[
  ⟨⟨["out"], [], [imp "good" "out" "g", imp "bad" "out" "b", set "out" (.list .empty)]⟩,
    [("good", 2), ("bad", 1)]⟩,
  ⟨⟨["out"], [], [set "out" (.list .empty), effect (.append (global "out") (int 1)),
    effect (.index (global "out") (int 2))]⟩, []⟩,
  ⟨⟨["out"], [], [set "out" (.list .empty)]⟩, []⟩]

-- The provider that succeeded remains cached. Failed modules can be tried again.
#guard
  match load #[] failing 0 with
  | .error (.initialization 1 (.runtime (.indexRange 2 1))) first =>
    let appended : List Lists.Value := [.scalar (.int 1)]
    (first.cache.map Prod.fst) == [2] && decide (lists first = [([], true), (appended, false)]) &&
      (match load #[] failing 1 first with
       | .error (.initialization 1 (.runtime (.indexRange 2 1))) retried =>
         (retried.cache.map Prod.fst) == [2] &&
           decide (lists retried = [([], true), (appended, false), (appended, false)])
       | _ => false)
  | _ => false

#guard
  let entry : Entry := ⟨⟨[], [], [imp "absent" "out" "dep"]⟩, []⟩
  (match load #[] #[entry] 0 with
   | .error (.missingLabel 0 "absent") _ => true
   | _ => false) &&
  (match load #[] #[{ entry with labels := [("absent", 3)] }] 0 with
   | .error (.unknownModule 3) _ => true
   | _ => false) &&
  (match load #[] #[⟨⟨[], [], [imp "leaf" "absent" "dep"]⟩, [("leaf", 1)]⟩, leaf] 0 with
   | .error (.initialization 0 (.missingExport "leaf" "absent")) session =>
     (session.cache.map Prod.fst) == [1]
   | _ => false)

end Silmaril.Languages.Starlark.Modules.Loader

module

import Silmaril.Languages.Starlark.Modules.Thms
import Silmaril.Languages.Starlark.Modules.Loader.Thms
meta import Silmaril.Languages.Starlark.Modules.Loader.Defs
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs

namespace Silmaril.Languages.Starlark.Modules

open Functions
open Lists (State)

private def read (binding : Binding) : Lists.Expr := .read (.bound binding)
private def global (name : String) : Lowering.Expr := .atom (read (globalSlot name))
private def int (n : Int) : Lowering.Expr := .atom (.scalar (.int n))
private def note (marker : Int) (value : Lowering.Expr) : Lowering.Expr :=
  .callPos (global "note") [int marker, value]
private def length (value : Lowering.Expr) : Lowering.Expr :=
  .callPos (.atom (.builtin .len)) [value]

private def program : Program :=
  let events := globalSlot "events"
  let marker := fileSlot "marker"
  let value := fileSlot "value"
  let xs := fileSlot "xs"
  #[
    ⟨{ positional := [⟨marker, none⟩, ⟨value, none⟩] }, [], [⟨events, events⟩],
      .seq (.total (.atomic (.eval (.append (read events) (read marker)))))
        (.returnExpr (.atom (read value)))⟩,
    ⟨{ positional := [⟨xs, some (note 1 (.atom (.list .empty)))⟩] }, [], [],
      .seq (.total (.atomic (.eval (.append (read xs) (.scalar (.int 9))))))
        (.returnExpr (.atom (read xs)))⟩]

private def setup : List Command :=
  [.exec (.assignExpr "events" (.atom (.list .empty))), .exec (.define "note" 0)]

private def provider : Source := ⟨["events", "note", "use", "seed", "out"], [], setup ++ [
  .exec (.define "use" 1),
  .exec (.assignExpr "seed" (note 2 (.atom (.list (.cons (.list .empty) .empty))))),
  .exec (.evalExpr (.branch (global "seed") (note 3 (length (global "seed"))) (note 99 (int 0)))),
  .exec (.assignExpr "out" (.logical .or (note 4 (global "seed")) (note 99 (int 0))))]⟩

private def failing : Source := ⟨["events", "note", "out"], [], setup ++ [
  .exec (.assignExpr "out" (length (note 1 (int 9)))), .exec (.evalExpr (note 99 (int 0)))]⟩

private def noImports : Catalog := fun _ => none

-- Inspect the exact namespace before caller restoration or publication.
#guard
  match runCommands program noImports failing.commands (enter failing {}) with
  | .error (.runtime (.builtinType .len (.scalar (.int 9)))) state =>
    match state.bindingValue (globalSlot "out"), state.bindingValue (globalSlot "events") with
    | .error (.uninitialized target), .ok (.list address) =>
      target == globalSlot "out" && decide (state.heap[address]? = some ⟨.list [.scalar (.int 1)], false⟩)
    | _, _ => false
  | _ => false

-- The failed module retains effects but is neither frozen nor cached.
#guard
  match Loader.load program #[⟨failing, []⟩] 0 { runtime := { iterators := [17] } } with
  | .error (.initialization 0 (.runtime (.builtinType .len (.scalar (.int 9))))) session =>
    session.cache.isEmpty && session.runtime.iterators == [17] &&
    (session.runtime.slots (globalSlot "out")).isNone &&
    decide (session.runtime.heap[3]? = some ⟨.list [.scalar (.int 1)], false⟩)
  | _ => false

-- Reading a later global through a native operand fails before its assignment.
#guard
  let source : Source := ⟨["out", "later"], [], [
    .exec (.assignExpr "out" (length (global "later"))),
    .exec (.assignExpr "later" (.atom (.list .empty)))]⟩
  match initializeModule program noImports source {} with
  | .error (.runtime (.uninitialized binding)) state =>
    binding == globalSlot "later" && state.heap.size == 2
  | _ => false

-- A loaded closure uses its stored default, frozen even though no global directly names the list.
private def rejectsDefault (published : Published) (state : State) (address : Lists.Address) : Bool :=
  let consumer : Source := ⟨[], [], [.load "provider" [⟨"use", "imported"⟩],
    .exec (.evalExpr (.callPos (.atom (read (fileSlot "imported"))) []))]⟩
  match initializeModule program (fun _ => some published) consumer state with
  | .error (.runtime (.frozen rejected)) _ => rejected == address
  | _ => false

#guard
  match initializeModule program noImports provider {} with
  | .ok published state =>
    match published.exports.lookup "seed", published.exports.lookup "out", published.exports.lookup "events",
        published.exports.lookup "use" with
    | some (.list seed), some (.list out), some (.list events), some (.function address) =>
      match state.heap[out]?, getClosure address state with
      | some ⟨.list [.list child], true⟩, .ok closure _ =>
        match closure.defaults.lookup (fileSlot "xs") with
        | some (.list default) =>
          seed == out && decide (state.heap[child]? = some ⟨.list [], true⟩) &&
          decide (state.heap[events]? = some ⟨.list ([1, 2, 3, 4].map fun n => .scalar (.int n)), true⟩) &&
          rejectsDefault published state default
        | _ => false
      | _, _ => false
    | _, _, _, _ => false
  | _ => false

-- The finite loader publishes in dependency order, with only the consumer's global exported.
#guard
  let imported := Lowering.Expr.atom (read (fileSlot "imported"))
  let consumer : Source := ⟨["size"], [], [.load "provider" [⟨"out", "imported"⟩],
    .exec (.assignExpr "size" (length imported))]⟩
  let manifest : Loader.Manifest := #[⟨consumer, [("provider", 1)]⟩, ⟨provider, []⟩]
  match Loader.load program manifest 0 with
  | .ok published session =>
    decide (published.exports = [("size", .scalar (.int 1))]) && (session.cache.map Prod.fst) == [0, 1]
  | _ => false

-- Validation visits native operands even when evaluation would skip them.
#guard
  let bad : Lowering.Expr := .call (.atom (.builtin .len)) [] [("x", int 0), ("x", int 1)] none none
  let source : Source := ⟨["out"], [], [
    .exec (.assignExpr "out" (.atom (.list .empty))), .exec (.evalExpr (.logical .or (int 1) bad))]⟩
  match initializeModule program noImports source {} with
  | .error (.syntax (.duplicateExplicitKeyword "x")) state => state.heap.isEmpty
  | _ => false

end Silmaril.Languages.Starlark.Modules

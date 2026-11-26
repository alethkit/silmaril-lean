module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open scoped Functions.Lowering.Quote
open Defaults
open Defaults.Nested.Sequence.Recursive (Site)
open Defaults.Nested.Sequence.Recursive.Call.Named (Mapping)
open Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance (Entry)
open Functions (Program)

private def globals : List String := ["data", "factory", "escaped", "late", "alias", "result", "after"]
private def int (n : Int) : Functions.Lowering.Expr := .atom (.scalar (.int n))
private def boxed (n : Int) : Functions.Lowering.Expr := .list [int n]
private def localRead (name : String) : Functions.Lowering.Expr := Leaf.readOperand (fileSlot name)
private def globalRead (name : String) : Functions.Lowering.Expr := Leaf.readOperand (globalSlot name)

private def factoryBlock : Assignment.LexicalBlock := ⟨["value", "child", "copy"], [], globals⟩
private def childKeywords : List PlainKeywordParameter :=
  [.defaulted ⟨"key", starlark%[value], localRead "value", [fileSlot "value"]⟩]

private def childBody : Body.Suite :=
  .assign "marked" starlark%[[44]] (.assign "probe" starlark%[key[0]]
    (.assign "seen" starlark%[value[0]] (.ret starlark%[late])))

private def child : Site factoryBlock childKeywords (some "rest") (some "extras") where
  name := "child"
  target := by decide
  parameters := ⟨["first"], []⟩
  source := childBody.source
  binders := ["marked", "probe", "seen"]
  locals := ["marked", "probe", "seen"]
  collects := .seq (.assign _ _) (.seq (.assign _ _) (.seq (.assign _ _) (.ret _)))
  localOrder := .keep (by decide) (.keep (by decide) (.keep (by decide) .nil))
  body := ⟨.seq (.assignExpr (fileSlot "marked") (boxed 44))
    (.seq (.assignExpr (fileSlot "probe") (.index (localRead "key") (int 0)))
      (.seq (.assignExpr (fileSlot "seen") (.index (localRead "value") (int 0)))
        (.returnExpr (globalRead "late")))), [fileSlot "key", fileSlot "value", globalSlot "late"]⟩
  free := [⟨fileSlot "value", fileSlot "value"⟩, ⟨globalSlot "late", globalSlot "late"⟩]
  selects := .owned (.owned (by decide))
    (.enclosing (.enclosing (by decide) (by decide)) (.module (.module (by decide) (by decide) (by decide)) .nil))
  defaults := []
  lexical := .nil

private def returned : Entry factoryBlock := ⟨0, childKeywords, some "rest", some "extras", child⟩

private def factoryTail : Statement :=
  .seq (.assign "copy" starlark%[child])
    (.seq (.assign "value" starlark%[[52]]) (.ret (some starlark%[copy])))

private def factoryTailCode : ResolvedBody :=
  ⟨.seq (.assignExpr (fileSlot "copy") (localRead "child"))
    (.seq (.assignExpr (fileSlot "value") (boxed 52)) (.returnExpr (localRead "copy"))),
    [fileSlot "child", fileSlot "copy"]⟩

private def factory : Site (moduleLex globals) [] none none .global where
  name := "factory"
  target := by decide
  parameters := ⟨["value"], []⟩
  source := .seq child.statement factoryTail
  binders := ["child", "copy", "value"]
  locals := ["child", "copy"]
  collects := .seq (.define _ _ _) (.seq (.assign _ _) (.seq (.assign _ _) (.ret _)))
  localOrder := .keep (by decide) (.keep (by decide) (.skip (by decide) .nil))
  body := ⟨.seq (.define (fileSlot "child") 0) factoryTailCode.code, child.reads ++ factoryTailCode.reads⟩
  free := [⟨globalSlot "late", globalSlot "late"⟩]
  selects := .owned (.owned (by decide)) (.module (.module (by decide) (by decide) (by decide))
    (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil)))
  defaults := []
  lexical := .nil

private def root : Root globals where
  keywords := []
  varargs := none
  kwargs := none
  site := factory
  lexical := .nil
  seed := #[]
  bodyTable := #[child.declaration]
  children := [(0, child.declaration)]
  returned := some returned
  suite := by
    refine .define (rest := factoryTail) (tail := factoryTailCode)
      (childTable := #[]) (descendants := []) (later := []) child (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil) ?_ ?_
    · refine .plain (.straight (source := childBody) ?_)
      refine .assign (by decide) (.list (.int 44)) ?_
      refine .assign (by decide) (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0)) ?_
      refine .assign (by decide) (.index (.read (by decide) (.enclosing (by decide) (by decide))
        (.enclosing (by decide) (by decide))) (.int 0)) ?_
      exact .ret (.read (by decide) (.global (by decide) (by decide) (by decide))
        (.module (by decide) (by decide) (by decide)))
    · exact .assign (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide)))
        (.copy (name := "child") (by decide) rfl)
        (.assign (by decide) (.list (.int 52)) .forget (.returnLocal (by decide) (by decide) rfl))

private theorem fromGlobal {name : String} (member : name ∈ globals)
    (legal : name.toList.head? ≠ some '$') :
    Body.Operand (moduleLex globals) (.scalar (.read name)) (globalRead name) [globalSlot name] :=
  .read legal (.global (by simp [moduleLex]) (by simp [moduleLex]) member)
    (.module (by simp [moduleLex]) (by simp [moduleLex]) member)

private def make : Invocation globals where
  callee := "factory"
  calleeGlobal := by decide
  legal := by decide
  destination := "escaped"
  destinationGlobal := by decide
  arguments := [starlark%[data]]
  codes := [globalRead "data"]
  reads := [globalSlot "data"]
  operands := .cons (fromGlobal (by decide) (by decide)) .nil
  keywords := .empty

private def mapping (bad : Bool) : Mapping (moduleLex globals) :=
  if bad then ⟨[(.string "key", starlark%[8])], [(.atom (.string "key"), int 8)], [],
    .entry (.string "key") (.plain (.int 8)) .empty⟩
  else ⟨[(.string "extra", starlark%[late])], [(.atom (.string "extra"), globalRead "late")], [globalSlot "late"],
    .entry (.string "extra") (.plain (fromGlobal (by decide) (by decide))) .empty⟩

private def invoke (bad : Bool) : Invocation globals where
  callee := "alias"
  calleeGlobal := by decide
  legal := by decide
  destination := "result"
  destinationGlobal := by decide
  arguments := []
  codes := []
  reads := []
  operands := .nil
  keywords := ⟨[("another", starlark%[[61]])], [("another", boxed 61)], [], .cons (.list (.int 61)) .nil, by decide⟩
  star := some (.list (.cons (fromGlobal (name := "data") (by decide) (by decide))
    (.cons (fromGlobal (name := "data") (by decide) (by decide)) .nil)))
  mapping := some (mapping bad)

private def commands (bad : Bool) : List Resolve.Command :=
  [.assign "data" starlark%[[31]], root.command, make.source, .assign "late" starlark%[[83]],
   .assign "alias" starlark%[escaped], (invoke bad).source, .assign "after" starlark%[[99]]]

private def code (bad : Bool) : List Modules.Command :=
  [.exec (.assignExpr "data" (boxed 31)), .exec (.define "factory" 1), .exec (.assignExpr "escaped" make.code),
   .exec (.assignExpr "late" (boxed 83)), .exec (.assignExpr "alias" (globalRead "escaped")),
   .exec (.assignExpr "result" (invoke bad).code), .exec (.assignExpr "after" (boxed 99))]

private def exports : Environment :=
  update (update (update (update (update (update (update (fun _ => none) "data" none)
    "factory" (some root.callable)) "escaped" (some (.nested returned))) "late" none)
    "alias" (some (.nested returned))) "result" none) "after" none

private theorem plan (bad : Bool) : Plan globals (fun _ => none) (commands bad) #[] (code bad) root.table exports := by
  refine .assign (by decide) (.list (.int 31)) .forget (.define root ?_)
  refine .invoke make root.callable rfl (.assign (by decide) (.list (.int 83)) .forget ?_)
  refine .assign (by decide) (fromGlobal (by decide) (by decide)) (.copy (name := "escaped") rfl) ?_
  exact .invoke (invoke bad) (.nested returned) rfl (.assign (by decide) (.list (.int 99)) .forget .done)

example (bad : Bool) {resolved : ResolvedModule} (checked : resolve (commands bad) = .ok resolved)
    (caller : Lists.State) :
    ∃ reached, ExecutesAll globals (enter resolved.source caller) (commands bad) reached ∧
      runModule (commands bad) (fun _ => none) caller = .ok (finish resolved.source caller reached) ∧
      ∀ published final, finish resolved.source caller reached = .ok published final →
        PublishedLive exports resolved.program published final := by
  have checkedPlan : Plan (Trace.names (commands bad)) (fun _ => none) (commands bad) #[] (code bad) root.table exports := plan bad
  obtain ⟨out, source, _, _, exactResult, published⟩ := module_agrees checkedPlan checked (fun _ => none) caller
  exact ⟨out, source, exactResult, published⟩

#guard
  match runModule (commands false) (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "escaped", published.exports.lookup "alias", published.exports.lookup "data",
      published.exports.lookup "late", published.exports.lookup "result" with
    | some (.function escaped), some (.function alias), some (.list data), some (.list late), some (.list result) =>
      match final.heap[escaped]? with
      | some ⟨.function closure, true⟩ =>
        escaped == alias && late == result && closure.declaration == 0 &&
        closure.defaults == [(fileSlot "key", .list data)] &&
        final.heap[data]? == some ⟨.list [.scalar (.int 31)], true⟩ &&
        final.heap[late]? == some ⟨.list [.scalar (.int 83)], true⟩ &&
        (match closure.captures with
        | [value, global] =>
          (match final.heap[value.address]? with
          | some ⟨.binding (some (.list rebound)), true⟩ =>
            final.heap[rebound]? == some ⟨.list [.scalar (.int 52)], true⟩
          | _ => false) && final.heap[global.address]? == some ⟨.binding (some (.list late)), false⟩
        | _ => false)
      | _ => false
    | _, _, _, _, _ => false
  | _ => false

#guard
  let caller : Lists.State := { iterators := [123] }
  match runModule (commands true) (fun _ => none) caller, resolve (commands true) with
  | .ok (.error (.runtime .indexTarget) final), .ok resolved =>
    let entered := enter resolved.source caller
    let cell name := (entered.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    let lists := final.heap.toList.filterMap fun cell => match cell.contents with
      | .list [.scalar (.int value)] => some (value, cell.frozen)
      | _ => none
    let tuples := final.heap.toList.countP fun cell => match cell.contents with | .tuple .. => true | _ => false
    let dicts := final.heap.toList.countP fun cell => match cell.contents with | .dict .. => true | _ => false
    lists == [(31, false), (52, false), (83, false), (61, false), (44, false)] && tuples == 1 && dicts == 2 &&
    cell "escaped" == cell "alias" && cell "result" == some ⟨.binding none, false⟩ &&
    cell "after" == some ⟨.binding none, false⟩ && (final.slots (globalSlot "alias")).isNone &&
    final.iterators == [123]
  | _, _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

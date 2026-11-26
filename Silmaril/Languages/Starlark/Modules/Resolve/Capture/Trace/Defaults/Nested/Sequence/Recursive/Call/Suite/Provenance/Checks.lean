module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance

open scoped Functions.Lowering.Quote
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Functions (Program)

private def block : LexicalBlock :=
  ⟨["values", "index", "first", "alias", "marker", "copy", "replacement", "firstValue", "selected", "after"], [], []⟩

private def readLocal (name : String) : Functions.Lowering.Expr := Leaf.readOperand (fileSlot name)

private def listInt (value : Int) : Functions.Lowering.Expr := .list [.atom (.scalar (.int value))]

private def original : Site block where
  name := "first"
  target := by decide
  parameters := ⟨[], [("saved", starlark%[values])]⟩
  source := .ret (some starlark%[saved[index]])
  binders := []
  locals := []
  collects := .ret _
  localOrder := .nil
  body := ⟨.returnExpr (.index (readLocal "saved") (readLocal "index")), [fileSlot "saved", fileSlot "index"]⟩
  free := [⟨fileSlot "index", fileSlot "index"⟩]
  selects := .owned (.owned (by decide)) (.enclosing (.enclosing (by decide) (by decide)) .nil)
  defaults := [⟨"saved", starlark%[values], readLocal "values", [fileSlot "values"]⟩]
  lexical := .cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil

private theorem original_body (seed : Program) :
    Elaborates original.block empty original.source seed original.body seed [] :=
  .plain (.straight (.ret (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
    (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide))))))

private def replacement : Site block where
  name := "replacement"
  target := by decide
  parameters := ⟨["required"], []⟩
  source := .ret (some starlark%[required])
  binders := []
  locals := []
  collects := .ret _
  localOrder := .nil
  body := ⟨.returnExpr (readLocal "required"), [fileSlot "required"]⟩
  free := []
  selects := .owned (.owned (by decide)) .nil
  defaults := []
  lexical := .nil

private theorem replacement_body (seed : Program) :
    Elaborates replacement.block empty replacement.source seed replacement.body seed [] :=
  .plain (.straight (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide)))))

private def aliasCall : Invocation block :=
  ⟨"copy", by decide, by decide, "firstValue", by decide, [], [], [], .nil⟩

private inductive Mode where
  | success | arity | operand

private def selectedCall (mode : Mode) : Invocation block where
  callee := "first"
  calleeOwned := by decide
  calleeLegal := by decide
  destination := "selected"
  destinationOwned := by decide
  arguments := match mode with
    | .success => [starlark%[[firstValue]]]
    | .arity => []
    | .operand => [starlark%[[73]], starlark%[[0][1]], starlark%[[77]]]
  codes := match mode with
    | .success => [.list [readLocal "firstValue"]]
    | .arity => []
    | .operand => [listInt 73, .index (listInt 0) (.atom (.scalar (.int 1))), listInt 77]
  argumentReads := match mode with
    | .success => [fileSlot "firstValue"]
    | _ => []
  operands := by
    cases mode with
    | success => exact .cons (.list (.read (by decide) (.owned (by decide)) (.owned (by decide)))) .nil
    | arity => exact .nil
    | operand =>
      exact .cons (.list (.int 73))
        (.cons (.index (.list (.int 0)) (.int 1)) (.cons (.list (.int 77)) .nil))

private def tail : Body.Suite :=
  .assign "after" starlark%[[99]] (.ret starlark%[selected[0]])

private def tailCode : ResolvedBody :=
  ⟨.seq (.assignExpr (fileSlot "after") (listInt 99))
    (.returnExpr (.index (readLocal "selected") (.atom (.scalar (.int 0))))), [fileSlot "selected"]⟩

private def beforeReplacement := [("alias", starlark%[first]), ("marker", starlark%[[17]]), ("copy", .scalar (.read "alias"))]
private def afterReplacement := [("first", starlark%[replacement]), ("alias", starlark%[0])]

private def source (mode : Mode) : Statement :=
  .seq original.statement (Body.prependSource beforeReplacement
    (.seq replacement.statement (Body.prependSource afterReplacement
      (.seq aliasCall.source (.seq (selectedCall mode).source tail.source)))))

private def compiledBody (mode : Mode) (seed : Program) : ResolvedBody :=
  ⟨.seq (.define (fileSlot "first") seed.size)
      (Body.prependCode [("alias", readLocal "first"), ("marker", listInt 17), ("copy", readLocal "alias")]
        (.seq (.define (fileSlot "replacement") (seed.size + 1))
          (Body.prependCode [("first", readLocal "replacement"), ("alias", .atom (.scalar (.int 0)))]
            (.seq aliasCall.code (.seq (selectedCall mode).code tailCode.code))))),
    original.reads ++ ([fileSlot "first"] ++ ([] ++ ([fileSlot "alias"] ++
      (replacement.reads ++ ([fileSlot "replacement"] ++ ([] ++
        (aliasCall.reads ++ ((selectedCall mode).reads ++ tailCode.reads))))))))⟩

private def emitted (seed : Program) : Program := (seed.push original.declaration).push replacement.declaration

private theorem profile (mode : Mode) (seed : Program) :
    Elaborates block empty (source mode) seed (compiledBody mode seed) (emitted seed)
      [(seed.size, original.declaration), (seed.size + 1, replacement.declaration)] := by
  have ending : Body.Elaborates block tail tailCode.code tailCode.reads :=
    .assign (by decide) (.list (.int 99))
      (.ret (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0)))
  have assembled := Elaborates.define (locals := empty) original (original_body seed)
    (.assign (name := "alias") (by decide) (.read (by decide) (.owned original.target) (.owned original.target))
      (.copy original.target rfl)
      (.assign (name := "marker") (by decide) (.list (.int 17)) .forget
        (.assign (name := "copy") (by decide) (.read (name := "alias") (by decide) (.owned (by decide)) (.owned (by decide)))
          (.copy (by decide) rfl)
          (.define replacement (replacement_body (seed.push original.declaration))
            (.assign (name := "first") (by decide)
              (.read (by decide) (.owned replacement.target) (.owned replacement.target))
              (.copy replacement.target rfl)
              (.assign (name := "alias") (by decide) (.int 0) .forget
                (.invoke aliasCall ⟨seed.size, original⟩ rfl
                  (.invoke (selectedCall mode) ⟨(seed.push original.declaration).size, replacement⟩ rfl
                    (.plain (.straight ending))))))))))
  have firstName : original.name = "first" := rfl
  have replacementName : replacement.name = "replacement" := rfl
  simpa [source, compiledBody, emitted, beforeReplacement, afterReplacement, Body.prependSource,
    Body.prependCode, readLocal, listInt, fileSlot, firstName, replacementName, Array.size_push] using assembled

example (mode : Mode) (seed : Program) :
    compileBody ⟨block.context, .local⟩ (source mode) seed = .ok (compiledBody mode seed, emitted seed) :=
  compiles (profile mode seed)

example (mode : Mode) (seed : Program) {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations (emitted seed) resolved.program)
    {free : List Functions.FreeName} (selected : Selects block (compiledBody mode seed).reads free)
    (state : Lists.State) (floor : Nat) (frame : Body.Frame block free floor state)
    (distinct : RootCall.DistinctOwned state) :
    let available := Functions.withoutDeclaration (List.range resolved.program.size) (emitted seed).size
    ∃ out, Runs block state (source mode) (compiledBody mode seed).code out ∧
      Functions.Exec resolved.program available state (compiledBody mode seed).code out ∧
      Functions.denoteBody resolved.program available (compiledBody mode seed).code state = out := by
  have selection : Selects block ([] ++ (compiledBody mode seed).reads ++ []) free := by simpa using selected
  obtain ⟨out, trace, _, _, exec, meaning⟩ :=
    runs (profile mode seed) checked table _ (entry_guard (profile mode seed) table) selection state frame distinct
  exact ⟨out, trace, exec, meaning⟩

private def commands (mode : Mode) : List Command :=
  [.assign "values" starlark%[[11,22]], .define "factory" (.required ["values", "index"]) (source mode),
   .assign "result" (.call starlark%[factory] [starlark%[values], starlark%[1]] [] none none),
   .assign "finished" starlark%[[91]]]

#guard
  match runModule (commands .success) (fun _ => none) {} with
  | .ok (.ok published final) =>
    published.exports.lookup "result" == some (.scalar (.int 22)) &&
    final.heap.any (fun cell => cell.contents == .list [.scalar (.int 99)])
  | _ => false

private def fails (mode : Mode) (expected : Lists.Error) (operandAllocations : Bool) : Bool :=
  let source := commands mode
  let caller : Lists.State := { iterators := [123] }
  match resolve source, runModule source (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime reached) final) =>
    let entry := enter resolved.source caller
    let moduleCell name := (entry.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    let hasList (n : Int) := final.heap.any (fun cell => cell.contents == .list [.scalar (.int n)])
    let restoredLocals :=
      match moduleCell "factory" with
      | some ⟨.binding (some (.function address)), false⟩ =>
        final.heap[address + 8]? == some ⟨.binding (some (.scalar (.int 22))), false⟩ &&
        final.heap[address + 9]? == some ⟨.binding none, false⟩ &&
        final.heap[address + 10]? == some ⟨.binding none, false⟩
      | _ => false
    reached == expected && hasList 17 && hasList 73 == operandAllocations &&
    hasList 0 == operandAllocations && !hasList 77 && !hasList 99 && !hasList 91 && restoredLocals &&
    moduleCell "result" == some ⟨.binding none, false⟩ && moduleCell "finished" == some ⟨.binding none, false⟩ &&
    (final.slots (globalSlot "factory")).isNone && final.iterators == [123]
  | _, _ => false

-- The rebound local selects the replacement's required parameter rather
-- than reusing the earlier closure's saved default.
#guard fails .arity (.missingArguments ["required"]) false
#guard fails .operand (.indexRange 1 1) true

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance

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
  parameters := ⟨["required"], [("offset", starlark%[1]), ("saved", starlark%[values])]⟩
  source := .ret (some starlark%[required[offset][saved[0]]])
  binders := []
  locals := []
  collects := .ret _
  localOrder := .nil
  body := ⟨.returnExpr (.index (.index (readLocal "required") (readLocal "offset"))
    (.index (readLocal "saved") (.atom (.scalar (.int 0))))),
    [fileSlot "required", fileSlot "offset", fileSlot "saved"]⟩
  free := []
  selects := .owned (.owned (by decide)) (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil))
  defaults := [⟨"offset", starlark%[1], .atom (.scalar (.int 1)), []⟩,
    ⟨"saved", starlark%[values], readLocal "values", [fileSlot "values"]⟩]
  lexical := .cons (.int 1) (.cons (.read (by decide) (.owned (by decide)) (.owned (by decide))) .nil)

private theorem replacement_body (seed : Program) :
    Elaborates replacement.block empty replacement.source seed replacement.body seed [] :=
  .plain (.straight (.ret (.index
    (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
      (.read (by decide) (.owned (by decide)) (.owned (by decide))))
    (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0)))))

private def aliasCall : Invocation block :=
  ⟨"copy", by decide, by decide, "firstValue", by decide, [], [], [], .nil, .empty⟩

private inductive Mode where
  | success | missing | unknown | conflict | operand | surplus

private def keywordNames (mode : Mode) : List String :=
  match mode with
  | .success => ["offset"]
  | .missing => []
  | .surplus => ["other"]
  | .unknown => ["other", "required"]
  | .conflict => ["required", "other"]
  | .operand => ["other", "offset", "later"]

private def selectedKeywords (mode : Mode) : Call.Named.Operands block where
  source := (keywordNames mode).zip (match mode with
    | .success => [starlark%[values[0]]]
    | .missing => []
    | .surplus => [starlark%[[80]]]
    | .unknown | .conflict => [starlark%[[80]], starlark%[[81]]]
    | .operand => [starlark%[[80]], starlark%[[0][1]], starlark%[[77]]])
  codes := (keywordNames mode).zip (match mode with
    | .success => [.index (readLocal "values") (.atom (.scalar (.int 0)))]
    | .missing => []
    | .surplus => [listInt 80]
    | .unknown | .conflict => [listInt 80, listInt 81]
    | .operand => [listInt 80, .index (listInt 0) (.atom (.scalar (.int 1))), listInt 77])
  reads := match mode with
    | .success => [fileSlot "values"]
    | _ => []
  related := by
    cases mode with
    | success => exact .cons (.index (.read (by decide) (.owned (by decide)) (.owned (by decide))) (.int 0)) .nil
    | surplus => exact .cons (.list (.int 80)) .nil
    | missing => exact .nil
    | unknown | conflict => exact .cons (.list (.int 80)) (.cons (.list (.int 81)) .nil)
    | operand => exact .cons (.list (.int 80)) (.cons (.index (.list (.int 0)) (.int 1))
        (.cons (.list (.int 77)) .nil))
  distinct := by cases mode <;> decide

private def selectedCall (mode : Mode) : Invocation block where
  callee := "first"
  calleeOwned := by decide
  calleeLegal := by decide
  destination := "selected"
  destinationOwned := by decide
  arguments := match mode with
    | .success => [starlark%[[[firstValue]]]]
    | .missing => []
    | .surplus => [starlark%[[73]], starlark%[[74]], starlark%[[75]], starlark%[[76]]]
    | _ => [starlark%[[73]]]
  codes := match mode with
    | .success => [.list [.list [readLocal "firstValue"]]]
    | .missing => []
    | .surplus => [listInt 73, listInt 74, listInt 75, listInt 76]
    | _ => [listInt 73]
  argumentReads := match mode with
    | .success => [fileSlot "firstValue"]
    | _ => []
  operands := by
    cases mode with
    | success => exact .cons (.list (.list (.read (by decide) (.owned (by decide)) (.owned (by decide))))) .nil
    | missing => exact .nil
    | unknown | conflict | operand => exact .cons (.list (.int 73)) .nil
    | surplus =>
      exact .cons (.list (.int 73)) (.cons (.list (.int 74)) (.cons (.list (.int 75)) (.cons (.list (.int 76)) .nil)))
  keywords := selectedKeywords mode

private def tail : Body.Suite :=
  .assign "after" starlark%[[99]] (.ret starlark%[selected])

private def tailCode : ResolvedBody :=
  ⟨.seq (.assignExpr (fileSlot "after") (listInt 99))
    (.returnExpr (readLocal "selected")), [fileSlot "selected"]⟩

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
      (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide))))
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
  [.assign "values" starlark%[[0,22]], .define "factory" (.required ["values", "index"]) (source mode),
   .assign "result" (.call starlark%[factory] [starlark%[values], starlark%[1]] [] none none),
   .assign "finished" starlark%[[91]]]

#guard
  match runModule (commands .success) (fun _ => none) {} with
  | .ok (.ok published final) =>
    published.exports.lookup "result" == some (.scalar (.int 22)) &&
    final.heap.any (fun cell => cell.contents == .list [.scalar (.int 99)])
  | _ => false

private def fails (mode : Mode) (expected : Lists.Error) (allocations : List Int) : Bool :=
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
    let operandLists (cell : Lists.Cell) : Option Int := match cell.contents with
      | .list [.scalar (.int n)] => if n == 17 then none else some n
      | _ => none
    reached == expected && hasList 17 && final.heap.toList.filterMap operandLists == allocations && restoredLocals &&
    moduleCell "result" == some ⟨.binding none, false⟩ && moduleCell "finished" == some ⟨.binding none, false⟩ &&
    (final.slots (globalSlot "factory")).isNone && final.iterators == [123]
  | _, _ => false

#guard fails .missing (.missingArguments ["required"]) []
#guard fails .unknown (.unexpectedKeyword "other") [73, 80, 81]
#guard fails .conflict (.multipleArgumentValues "required") [73, 80, 81]
#guard fails .operand (.indexRange 1 1) [73, 80, 0]
#guard fails .surplus (.arity 3 4) [73, 74, 75, 76, 80]

-- The existing binder reports the unknown name on a keyword-only call
-- to a nullary function. Pinned Go has a special nullary diagnostic.
#guard
  match Functions.bindArguments {} [] ⟨[], [("other", .scalar (.int 1))]⟩ with
  | .error (.unexpectedKeyword "other") => true
  | _ => false

-- Raw normalized source can represent repeated names. Whole checked
-- resolution rejects those before the first operand error is reached.
#guard
  let invalid : Command := .define "factory" (.required [])
    (.ret (some (.call (.scalar (.read "factory")) []
      [("offset", starlark%[[0][1]]), ("offset", starlark%[2])] none none)))
  match resolve [invalid] with
  | .error (.validation (.syntax (.duplicateExplicitKeyword "offset"))) => true
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance

module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive

open scoped Functions.Lowering.Quote
open Assignment (LexicalBlock)
open Functions (FreeName Program)

private def enclosingBlock : LexicalBlock := ⟨["factory"], [], []⟩

private def factoryBlock : LexicalBlock := ⟨["x", "index", "relay", "copy"], enclosingBlock.owned, []⟩

private def relayBlock : LexicalBlock := ⟨["leaf"], factoryBlock.owned ++ factoryBlock.enclosing, []⟩

private def localRead (name : String) : Functions.Lowering.Expr := Leaf.readOperand (fileSlot name)

private def returnName (name : String) : Statement := .ret (some (.scalar (.read name)))

private def leafSuite : Body.Suite :=
  .assign "offset" starlark%[index] (.assign "alias" starlark%[x] (.ret starlark%[saved[offset]]))

private def leafParameters : Parameters := ⟨[], [("saved", starlark%[x])]⟩

private def leafSite : Site relayBlock where
  name := "leaf"
  target := by decide
  parameters := leafParameters
  source := leafSuite.source
  binders := ["offset", "alias"]
  locals := ["offset", "alias"]
  collects := .seq (.assign _ _) (.seq (.assign _ _) (.ret _))
  localOrder := .keep (by decide) (.keep (by decide) .nil)
  body := ⟨.seq (.assignExpr (fileSlot "offset") (localRead "index"))
    (.seq (.assignExpr (fileSlot "alias") (localRead "x"))
     (.returnExpr (.index (localRead "saved") (localRead "offset")))),
    [fileSlot "index", fileSlot "x", fileSlot "saved", fileSlot "offset"]⟩
  free := [⟨fileSlot "index", fileSlot "index"⟩, ⟨fileSlot "x", fileSlot "x"⟩]
  selects := .enclosing (.enclosing (by decide) (by decide))
    (.enclosing (.enclosing (by decide) (by decide))
      (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil)))
  defaults := [⟨"saved", starlark%[x], localRead "x", [fileSlot "x"]⟩]
  lexical := .cons (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide))) .nil

private theorem leafBody (seed : Program) :
    Elaborates leafSite.block leafSite.source seed leafSite.body seed [] :=
  .straight (.assign (by decide)
    (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide)))
    (.assign (by decide)
      (.read (by decide) (.enclosing (by decide) (by decide)) (.enclosing (by decide) (by decide)))
      (.ret (.index (.read (by decide) (.owned (by decide)) (.owned (by decide)))
        (.read (by decide) (.owned (by decide)) (.owned (by decide)))))))

private def relaySite (seed : Program) : Site factoryBlock where
  name := "relay"
  target := by decide
  parameters := ⟨[], []⟩
  source := .seq leafSite.statement (returnName "leaf")
  binders := ["leaf"]
  locals := ["leaf"]
  collects := .seq (.define _ _ _) (.ret _)
  localOrder := .keep (by decide) .nil
  body := ⟨.seq (.define (fileSlot "leaf") seed.size) (.returnExpr (localRead "leaf")),
    leafSite.reads ++ [fileSlot "leaf"]⟩
  -- The default reads x before the body's first free reference index.
  free := [⟨fileSlot "x", fileSlot "x"⟩, ⟨fileSlot "index", fileSlot "index"⟩]
  selects := .enclosing (.enclosing (by decide) (by decide))
    (.enclosing (.enclosing (by decide) (by decide)) (.owned (.owned (by decide)) .nil))
  defaults := []
  lexical := .nil

private theorem relayBody (seed : Program) :
    Elaborates (relaySite seed).block (relaySite seed).source seed (relaySite seed).body
      (seed.push leafSite.declaration) [(seed.size, leafSite.declaration)] :=
  .define leafSite .nil (leafBody seed) (.straight (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide)))))

private def factoryTail : Body.Suite := .assign "copy" starlark%[relay] (.ret starlark%[copy])

private def factorySite (seed : Program) : Site enclosingBlock where
  name := "factory"
  target := by decide
  parameters := ⟨["x", "index"], []⟩
  source := .seq (relaySite seed).statement factoryTail.source
  binders := ["relay", "copy"]
  locals := ["relay", "copy"]
  collects := .seq (.define _ _ _) (.seq (.assign _ _) (.ret _))
  localOrder := .keep (by decide) (.keep (by decide) .nil)
  body := ⟨.seq (.define (fileSlot "relay") (seed.size + 1))
    (.seq (.assignExpr (fileSlot "copy") (localRead "relay")) (.returnExpr (localRead "copy"))),
    [fileSlot "x", fileSlot "index", fileSlot "relay", fileSlot "copy"]⟩
  free := []
  selects := .owned (.owned (by decide)) (.owned (.owned (by decide))
    (.owned (.owned (by decide)) (.owned (.owned (by decide)) .nil)))
  defaults := []
  lexical := .nil

private def factoryTable (seed : Program) : Program :=
  (seed.push leafSite.declaration).push (relaySite seed).declaration

private theorem factoryBody (seed : Program) :
    Elaborates (factorySite seed).block (factorySite seed).source seed (factorySite seed).body (factoryTable seed)
      [(seed.size, leafSite.declaration), (seed.size + 1, (relaySite seed).declaration)] := by
  have last : Body.Elaborates factoryBlock factoryTail
      (.seq (.assignExpr (fileSlot "copy") (localRead "relay")) (.returnExpr (localRead "copy")))
      [fileSlot "relay", fileSlot "copy"] :=
    .assign (by decide) (.read (by decide) (.owned (by decide)) (.owned (by decide)))
      (.ret (.read (by decide) (.owned (by decide)) (.owned (by decide))))
  simpa [Array.size_push, Body.prependSource, Body.prependCode, relaySite, factorySite, factoryTable, Site.reads, Site.block, factoryBlock, Parameters.names, enclosingBlock] using
    (Elaborates.define (relaySite seed) .nil (relayBody seed) (.straight last))

example (seed : Program) :
    let final := factoryTable seed
    PreservesDeclarations seed final ∧ final[seed.size]? = some leafSite.declaration ∧
      final[seed.size + 1]? = some (relaySite seed).declaration := by
  obtain ⟨stable, emitted⟩ := links (factoryBody seed)
  exact ⟨stable, emitted (seed.size, leafSite.declaration) (by simp),
    emitted (seed.size + 1, (relaySite seed).declaration) (by simp)⟩

example (seed : Program) :
    compileBody ⟨factoryBlock.context, .local⟩ (factorySite seed).source seed =
      .ok ((factorySite seed).body, factoryTable seed) :=
  compiles (factoryBody seed)

-- The activation supplies every owned slot and uses the generic recursive
-- execution rule, even though the relay to be returned has a nested body.
example (seed : Program) (caller : Lists.State) (x : Lists.Value) (index : Int) :
    let site := factorySite seed
    let program := factoryTable seed
    let active := Functions.activate caller site.declaration []
      [(fileSlot "x", x), (fileSlot "index", .scalar (.int index))]
    ∃ out, Runs factoryBlock active site.source site.body.code out ∧
      Functions.denoteBody program (List.range program.size) site.body.code active = out ∧
      (Lists.Iteration.finishState (Leaf.returnTo caller out)).slots = caller.slots := by
  obtain ⟨out, ran, _, _, meaning, restored, _, _⟩ :=
    runs_activated (factorySite seed) (factoryBody seed) (factoryTable seed) (fun _ _ same => same)
      (List.range (factoryTable seed).size) caller caller [] .nil (by simp [Body.CaptureCells])
      [(fileSlot "x", x), (fileSlot "index", .scalar (.int index))]
  exact ⟨out, ran, meaning, restored⟩

private def noise : Command := .define "noise" (.required []) (.ret (some starlark%[0]))

private def factory (shadowed malformed : Bool) (failed : Bool := false) : Command :=
  let parameters := if malformed then { leafParameters with required := ["saved"] } else leafParameters
  let relay := Statement.define "relay" (.required (if shadowed then ["x"] else []))
    (.seq (.define "leaf" parameters.source leafSuite.source) (returnName "leaf"))
  let leading := if failed then
    [("marker", starlark%[[73]]), ("broken", starlark%[marker[1]]), ("later", starlark%[[99]])]
    else []
  .define "factory" (.required ["x", "index"]) (.seq relay (Body.prependSource leading factoryTail.source))

private def commands (shadowed malformed : Bool) (failed : Bool := false) : List Command :=
  [noise, .assign "values" starlark%[[11,22]], .assign "near" starlark%[[33,44]],
   factory shadowed malformed failed, .assign "relay_fn" starlark%[factory(values,1)],
   .assign "leaf_fn" (if shadowed then starlark%[relay_fn(near)] else starlark%[relay_fn()]),
   .assign "result" starlark%[leaf_fn()]]

private def checks (shadowed : Bool) : Bool :=
  let cmds := commands shadowed false
  match resolve cmds, runModule cmds (fun _ => none) {} with
  | .ok resolved, .ok (.ok published final) =>
    let get name := published.exports.lookup name
    let free := resolved.program.toList.map fun declaration => declaration.free.map FreeName.source
    free == [[], [fileSlot "index", fileSlot "x"], (if shadowed then [fileSlot "index"] else [fileSlot "x", fileSlot "index"]), []] &&
    get "result" == some (.scalar (.int (if shadowed then 44 else 22))) &&
    (match get "relay_fn", get "leaf_fn" with
    | some (.function relay), some (.function leaf) =>
      match final.heap[relay]?, final.heap[leaf]? with
      | some ⟨.function relayClosure, true⟩, some ⟨.function leafClosure, true⟩ =>
        match leafClosure.captures, leafClosure.defaults with
        | [index, x], [(saved, value)] =>
          relayClosure.declaration == 2 && leafClosure.declaration == 1 &&
          saved == fileSlot "saved" && some value == get (if shadowed then "near" else "values") &&
          (if shadowed then relayClosure.captures == [index] && x.address > relay
            else relayClosure.captures == [x, index] && x.address < relay) &&
          final.heap[x.address]? == some ⟨.binding (some value), true⟩
        | _, _ => false
      | _, _ => false
    | _, _ => false)
  | _, _ => false

#guard checks false
#guard checks true

#guard
  match resolve (commands false true) with
  | .error (.validation (.syntax (.duplicateParameter "saved"))) => true
  | _ => false

-- A reached index error after installing the relay retains that closure
-- and the marker allocation. Later statements and the relay call never run.
#guard
  let cmds := commands false false true
  let caller : Lists.State := { iterators := [123] }
  match resolve cmds, runModule cmds (fun _ => none) caller with
  | .ok resolved, .ok (.error (.runtime (.indexRange 1 1)) final) =>
    let entered := enter resolved.source caller
    let moduleCell name := (entered.slots (globalSlot name)).bind (fun slot => final.heap[slot.address]?)
    let reached := final.heap.toList.filterMap fun cell => match cell.contents with
      | .function closure => some closure.declaration
      | _ => none
    reached == [0, 3, 2] &&
    final.heap.back? == some ⟨.list [.scalar (.int 73)], false⟩ &&
    moduleCell "relay_fn" == some ⟨.binding none, false⟩ &&
    moduleCell "leaf_fn" == some ⟨.binding none, false⟩ &&
    moduleCell "result" == some ⟨.binding none, false⟩ &&
    (final.slots (globalSlot "factory")).isNone && final.iterators == [123]
  | _, _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive

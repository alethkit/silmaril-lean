module

import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Languages.Starlark.Functions.Comprehensions.Expression.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs
meta import Silmaril.Languages.Starlark.Functions.Comprehensions.Expression.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve

open scoped Functions.Lowering.Quote
open Lists

private def noImports : Catalog := fun _ => none

private def intValue (value : Int) : Lists.Value := .scalar (.int value)

private def mark : Command :=
  .define "mark" { positional := [⟨"tag", none⟩, ⟨"value", none⟩] }
    (.seq (.setIndex starlark%[events] starlark%[count[0]] starlark%[tag])
      (.seq (.addIndex starlark%[count] starlark%[0] starlark%[1]) (.ret (some starlark%[value]))))

private def logCommands : List Command :=
  [.assign "events" starlark%[[0, 0, 0, 0, 0, 0, 0, 0]], .assign "count" starlark%[[0]], mark]

private def listArgument : CompExpr :=
  .list ⟨starlark%[x], starlark%[mark(2, [4])], .yield starlark%[mark(3, x)]⟩

private def dictArgument : CompExpr :=
  .dict ⟨starlark%[(k, [v])], starlark%[mark(4, [("a", [10])])],
    .yield (starlark%[mark(5, k)], starlark%[mark(6, v)])⟩

private def skipped : CompExpr :=
  .list ⟨starlark%[x], starlark%[mark(99, len(1))], .yield starlark%[x]⟩

private def eventsMatch (state : State) (address : Address) (expected : List Int) : Bool :=
  state.heap[address]?.map Cell.contents == some (.list (expected.map intValue))

-- The returned call evaluates the callee before its positional operands.
-- Logical/conditional forms keep their values and skip their unused sites.
#guard
  let call := CompExpr.callPos starlark%[pick()]
    [.logical .or listArgument skipped,
     .branch (.plain starlark%[True]) dictArgument skipped,
     .callPos starlark%[len] [.plain starlark%[mark(8, range(11))]]]
  let commands := logCommands ++
    [.define "sink" { positional := [⟨"xs", none⟩, ⟨"d", none⟩, ⟨"last", none⟩] }
       (.ret (some starlark%[mark(9, (xs[0], d["a"], last))])),
     .define "pick" {} (.ret (some starlark%[mark(1, sink)])),
     .define "run" {} (.retCompExpr call),
     .assign "out" starlark%[run()],
     .assign "ok" starlark%[{(4, 10, 11): True}[out]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
      match published.exports.lookup "events" with
      | some (.list address) => eventsMatch state address [1, 2, 3, 4, 5, 6, 8, 9]
      | _ => false
  | _ => false

-- A skipped right-hand comprehension contributes no heap allocation.
#guard
  let stop := Functions.Comprehensions.Expression.plain (.atom (.scalar (.bool false)))
  let comp : Functions.Comprehensions.ListComp :=
    ⟨[], .name (fileSlot "x"), .atom (.list .empty), .yield (.atom (.scalar (.int 1)))⟩
  let expr := Functions.Comprehensions.Expression.logical .and stop (.list comp)
  let out := globalSlot "out"
  match Functions.run #[] (expr.body out), Functions.run #[] (expr.lower out) with
  | .ok .next direct, .ok .next lowered =>
    direct.heap.isEmpty && lowered.heap.isEmpty &&
      (direct.bindingValue out).toOption == some (.scalar (.bool false)) &&
      (lowered.bindingValue out).toOption == some (.scalar (.bool false))
  | _, _ => false

private def failedArgument : CompExpr :=
  .dict ⟨starlark%[row], starlark%[mark(3, rows)],
    .forIn starlark%[(k, [v])] starlark%[row]
      (.yield (starlark%[mark(4, k)], starlark%[mark(5, v)]))⟩

private def errorCommands (callee : Functions.Lowering.Resolve.SourceExpr) : List Command :=
  logCommands ++
    [.assign "rows" starlark%[[[("a", [4]), ([], [5])]]],
     .define "sink" { varargs := some "args" } (.ret (some starlark%[mark(7, args)])),
     .assignCompExpr "out" (.callPos callee
       [.list ⟨starlark%[x], starlark%[mark(2, [])], .yield starlark%[x]⟩,
        failedArgument, .plain starlark%[mark(6, 0)]])]

-- Compare the complete heap of both executions at a command boundary.
-- A failed middle argument skips later arguments and dispatch, keeps its
-- own effects and restores exactly the iterator stack of the caller.
private def checkFailure (callee : Functions.Lowering.Resolve.SourceExpr)
    (error : Lists.Error → Bool) (expected : List Int) : Bool :=
  match resolve (errorCommands callee) with
  | .ok resolved =>
    match resolved.source.commands.reverse with
    | .exec (.assignCompExpr name expr) :: reversed =>
      match runCommands resolved.program noImports reversed.reverse (enter resolved.source {}) with
      | .ok () entered =>
        let target := globalSlot name
        let guard := entered.heap.size
        let seeded := entered.write target (intValue 91)
        let before := { seeded with heap := seeded.heap.push ⟨.list [], false⟩, iterators := [guard] }
        let run := Functions.denoteBody resolved.program (List.range resolved.program.size)
        match run (expr.body target) before, run (expr.lower target) before with
        | .error first direct, .error second lowered =>
          error first && first == second && direct.heap == lowered.heap &&
            direct.iterators == [guard] && lowered.iterators == [guard] &&
            (direct.bindingValue target).toOption == some (intValue 91) &&
            (lowered.bindingValue target).toOption == some (intValue 91) &&
            match direct.bindingValue (globalSlot "events") with
            | .ok (.list address) => eventsMatch direct address expected
            | _ => false
        | _, _ => false
      | _ => false
    | _ => false
  | _ => false

#guard checkFailure starlark%[mark(1, sink)] (fun | .unhashableKey (.list _) => true | _ => false)
  [1, 2, 3, 4, 5, 4, 5, 0]
#guard checkFailure starlark%[mark(1, [])[1]] (· == .indexRange 1 0)
  [1, 0, 0, 0, 0, 0, 0, 0]

-- Checking still visits skipped source nodes before execution.
#guard
  let invalid := CompExpr.list ⟨starlark%[(x, xs[0])], starlark%[[]], .yield starlark%[x]⟩
  match resolve [.assignCompExpr "out" (.branch (.plain starlark%[True]) listArgument invalid),
    mark, .assign "events" starlark%[[]], .assign "count" starlark%[[0]]] with
  | .error .unsupportedComprehensionTarget => true
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve

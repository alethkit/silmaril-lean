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
private def checkAssignmentFailure (commands : List Command)
    (error : Lists.Error → Bool) (expected : List Int) : Bool :=
  match resolve commands with
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
            (direct.bindings (Functions.Comprehensions.argumentSlot 0)).isNone &&
            (lowered.bindings (Functions.Comprehensions.argumentSlot 0)).isNone &&
            match direct.bindingValue (globalSlot "events") with
            | .ok (.list address) => eventsMatch direct address expected
            | _ => false
        | _, _ => false
      | _ => false
    | _ => false
  | _ => false

private def checkFailure (callee : Functions.Lowering.Resolve.SourceExpr)
    (error : Lists.Error → Bool) (expected : List Int) : Bool :=
  checkAssignmentFailure (errorCommands callee) error expected

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

private def markedCallee : CompExpr :=
  .branch (.list ⟨starlark%[x], starlark%[mark(1, [True])], .yield starlark%[mark(2, x)]⟩)
    (.plain starlark%[sink]) (.plain starlark%[len(1)])

-- Comprehensions occur inside the callee and in each non-positional form.
-- The fixtures use a growing event counter so any repeated stage is observable.
#guard
  let call := CompExpr.call markedCallee [.plain starlark%[mark(3, 9)]]
    [("k", .list ⟨starlark%[x], starlark%[mark(4, [10])], .yield starlark%[mark(5, x)]⟩)]
    (some (.list ⟨starlark%[x], starlark%[mark(6, [11])], .yield starlark%[mark(7, x)]⟩))
    (some (.dict ⟨starlark%[(n, v)], starlark%[mark(8, [("z", 12)])], .yield (starlark%[n], starlark%[v])⟩))
  let commands :=
    [.assign "events" starlark%[[0, 0, 0, 0, 0, 0, 0, 0, 0]], .assign "count" starlark%[[0]], mark,
     .define "sink" { positional := [⟨"a", none⟩, ⟨"b", none⟩, ⟨"k", none⟩, ⟨"z", none⟩] }
       (.ret (some starlark%[mark(9, (a, b, k[0], z))])),
     .define "run" {} (.retCompExpr call), .assign "out" starlark%[run()],
     .assign "ok" starlark%[{(9, 11, 10, 12): True}[out]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
      match published.exports.lookup "events" with
      | some (.list address) => eventsMatch state address [1, 2, 3, 4, 5, 6, 7, 8, 9]
      | _ => false
  | _ => false

-- A mapping expression can still mutate the saved star value before expansion.
#guard
  let mapping := CompExpr.dict
    ⟨starlark%[(k, v)], starlark%[[("b", 2)]], .yield (starlark%[k], starlark%[bump(v)])⟩
  let commands :=
    [.assign "xs" starlark%[[1]],
     .define "bump" { positional := [⟨"value", none⟩] }
       (.seq (.setIndex starlark%[xs] starlark%[0] starlark%[9]) (.ret (some starlark%[value]))),
     .define "sink" { positional := [⟨"a", none⟩, ⟨"b", none⟩] } (.ret (some starlark%[(a, b)])),
     .assignCompExpr "out" (.call (.plain starlark%[sink]) [] [] (some (.plain starlark%[xs])) (some mapping)),
     .assign "ok" starlark%[{(9, 2): True}[out]]]
  match runModule commands noImports {} with
  | .ok (.ok published _) => published.exports.lookup "ok" == some (.scalar (.bool true))
  | _ => false

private def named : CompExpr := .list ⟨starlark%[x], starlark%[mark(3, [5])], .yield starlark%[x]⟩

private def spread : CompExpr := .list ⟨starlark%[x], starlark%[mark(4, [6])], .yield starlark%[x]⟩

private def mapping (entries : Functions.Lowering.Resolve.SourceExpr) : CompExpr :=
  .dict ⟨starlark%[(k, v)], entries, .yield (starlark%[k], starlark%[mark(6, v)])⟩

private def checkCallFailure (call : CompExpr) (error : Lists.Error → Bool)
    (expected : List Int) : Bool :=
  let commands := logCommands ++
    [.assign "rows" starlark%[[[("a", [4]), ([], [5])]]],
     .define "sink" { varargs := some "rest", keywordOnly := [⟨"k", some starlark%[0]⟩] }
       (.ret (some starlark%[mark(7, k)])),
     .assignCompExpr "out" call]
  checkAssignmentFailure commands error expected

-- Both expansions succeed before the binder detects the duplicate named key.
#guard checkCallFailure
  (.call markedCallee [] [("k", named)] (some spread) (some (mapping starlark%[mark(5, [("k", 8)])])))
  (· == .multipleArgumentValues "k") [1, 2, 3, 4, 5, 6, 0, 0]

-- A mapping key error or mapping type error wins over an invalid star value.
#guard checkCallFailure
  (.call markedCallee [] [("k", named)] (some (.plain starlark%[mark(4, 0)]))
    (some (mapping starlark%[mark(5, [(1, 8)])])))
  (· == .keywordMustBeString (intValue 1)) [1, 2, 3, 4, 5, 6, 0, 0]

#guard checkCallFailure
  (.call markedCallee [] [("k", named)] (some (.plain starlark%[mark(4, 0)]))
    (some (.list ⟨starlark%[x], starlark%[mark(5, [])], .yield starlark%[x]⟩)))
  (· == .invalidStarStar) [1, 2, 3, 4, 5, 0, 0, 0]

-- Once mapping validation passes, the star error wins over binding duplicates.
#guard checkCallFailure
  (.call markedCallee [] [("k", named)] (some (.plain starlark%[mark(4, 0)]))
    (some (mapping starlark%[mark(5, [("k", 8)])])))
  (· == .invalidStar) [1, 2, 3, 4, 5, 6, 0, 0]

-- A failing final operand precedes all expansion and unwinds its iterators.
#guard checkCallFailure
  (.call markedCallee [] [] (some (.plain starlark%[mark(4, 0)])) (some failedArgument))
  (fun | .unhashableKey (.list _) => true | _ => false) [1, 2, 4, 3, 4, 5, 4, 5]

-- A failure within the callee's comprehension skips every argument stage.
#guard checkCallFailure
  (.call (.branch failedArgument (.plain starlark%[sink]) (.plain starlark%[sink]))
    [] [("k", named)] (some spread) (some (mapping starlark%[mark(5, [("k", 8)])])))
  (fun | .unhashableKey (.list _) => true | _ => false) [3, 4, 5, 4, 5, 0, 0, 0]

-- Explicit duplicate names are rejected before execution, even in a skipped arm.
#guard
  let duplicate := CompExpr.call (.plain starlark%[len]) [] [("x", named), ("x", spread)] none none
  match resolve (logCommands ++
    [.assignCompExpr "out" (.branch (.plain starlark%[False]) duplicate (.plain starlark%[None]))]) with
  | .error (.validation (.syntax (.duplicateExplicitKeyword "x"))) => true
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve

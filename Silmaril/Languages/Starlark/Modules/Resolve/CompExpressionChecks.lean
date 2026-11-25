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
    (error : Lists.Error → Bool) (expected : List Int)
    (heapCheck : State → State → Bool := fun _ _ => true) : Bool :=
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
          error first && first == second && direct.heap == lowered.heap && heapCheck before direct &&
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

private def checkPlacementFailure (expression : CompExpr) (error : Lists.Error → Bool)
    (expected : List Int) (heapCheck : State → State → Bool := fun _ _ => true) : Bool :=
  let commands := logCommands ++
    [.assign "rows" starlark%[[[("a", [4]), ([], [5])]]],
     .define "sink" { varargs := some "rest", keywordOnly := [⟨"k", some starlark%[0]⟩] }
       (.ret (some starlark%[mark(7, k)])),
     .assignCompExpr "out" expression]
  checkAssignmentFailure commands error expected heapCheck

-- Both expansions succeed before the binder detects the duplicate named key.
#guard checkPlacementFailure
  (.call markedCallee [] [("k", named)] (some spread) (some (mapping starlark%[mark(5, [("k", 8)])])))
  (· == .multipleArgumentValues "k") [1, 2, 3, 4, 5, 6, 0, 0]

-- A mapping key error or mapping type error wins over an invalid star value.
#guard checkPlacementFailure
  (.call markedCallee [] [("k", named)] (some (.plain starlark%[mark(4, 0)]))
    (some (mapping starlark%[mark(5, [(1, 8)])])))
  (· == .keywordMustBeString (intValue 1)) [1, 2, 3, 4, 5, 6, 0, 0]

#guard checkPlacementFailure
  (.call markedCallee [] [("k", named)] (some (.plain starlark%[mark(4, 0)]))
    (some (.list ⟨starlark%[x], starlark%[mark(5, [])], .yield starlark%[x]⟩)))
  (· == .invalidStarStar) [1, 2, 3, 4, 5, 0, 0, 0]

-- Once mapping validation passes, the star error wins over binding duplicates.
#guard checkPlacementFailure
  (.call markedCallee [] [("k", named)] (some (.plain starlark%[mark(4, 0)]))
    (some (mapping starlark%[mark(5, [("k", 8)])])))
  (· == .invalidStar) [1, 2, 3, 4, 5, 6, 0, 0]

-- A failing final operand precedes all expansion and unwinds its iterators.
#guard checkPlacementFailure
  (.call markedCallee [] [] (some (.plain starlark%[mark(4, 0)])) (some failedArgument))
  (fun | .unhashableKey (.list _) => true | _ => false) [1, 2, 4, 3, 4, 5, 4, 5]

-- A failure within the callee's comprehension skips every argument stage.
#guard checkPlacementFailure
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

private def collect (operand : Functions.Lowering.Resolve.SourceExpr) : CompExpr :=
  .list ⟨starlark%[x], operand, .yield starlark%[x]⟩

private def lengthOf (operand : CompExpr) : CompExpr :=
  .callPos starlark%[len] [operand]

-- Parent displays and indexing preserve the order of their nested sites.
-- The returned value also checks that a child scope restores saved siblings.
#guard
  let expression := CompExpr.tupleDisplay
    [.listDisplay [collect starlark%[mark(1, [7])], .plain starlark%[mark(2, 8)]],
     .dictDisplay [(lengthOf (collect starlark%[mark(3, [0])]),
       .dict ⟨starlark%[(k, v)], starlark%[mark(4, [("a", 9)])], .yield (starlark%[k], starlark%[v])⟩)],
     .index (collect starlark%[mark(5, [10, 11])]) (lengthOf (collect starlark%[mark(6, [0])]))]
  let commands := logCommands ++
    [.define "run" {} (.retCompExpr expression), .assign "out" starlark%[run()],
     .assign "ok" starlark%[{(7, 8, 9, 11): True}[(out[0][0][0], out[0][1], out[1][1]["a"], out[2])]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
      match published.exports.lookup "events" with
      | some (.list address) => eventsMatch state address [1, 2, 3, 4, 5, 6, 0, 0]
      | _ => false
  | _ => false

private def isUnhashableList : Lists.Error → Bool
  | .unhashableKey (.list _) => true
  | _ => false

-- A failed middle element releases its iterators and skips later elements.
#guard
  let elements := [collect starlark%[mark(1, [7])], failedArgument, .plain starlark%[mark(2, 8)]]
  let expected := [1, 3, 4, 5, 4, 5, 0, 0]
  checkPlacementFailure (.listDisplay elements) isUnhashableList expected &&
    checkPlacementFailure (.tupleDisplay elements) isUnhashableList expected

-- List and tuple outer allocations require every element to succeed.
-- Dictionary display allocation precedes even a failing first key.
#guard
  let failed := Functions.Comprehensions.Expression.plain
    (.index (.atom (.scalar (.int 0))) (.atom (.scalar (.int 0))))
  let destination := globalSlot "out"
  let heapOnError := fun (expr : Functions.Comprehensions.Expression) =>
    match Functions.run #[] (expr.body destination), Functions.run #[] (expr.lower destination) with
    | .error .indexTarget direct, .error .indexTarget lowered =>
      if direct.heap == lowered.heap then some direct.heap else none
    | _, _ => none
  heapOnError (.listDisplay [failed]) == some #[] &&
    heapOnError (.tupleDisplay [failed]) == some #[] &&
    heapOnError (.dictDisplay [(failed, failed)]) == some #[⟨.dict [], false⟩]

-- Key failure skips its value and every later pair.
#guard checkPlacementFailure
  (.dictDisplay [(failedArgument, collect starlark%[mark(1, [7])]),
    (.plain starlark%[mark(2, 0)], .plain starlark%[0])])
  isUnhashableList [3, 4, 5, 4, 5, 0, 0, 0]

-- Hashability checks follow both operands. A failure in the value wins.
#guard checkPlacementFailure
  (.dictDisplay [(collect starlark%[mark(1, [])], .plain starlark%[mark(2, [])[1]]),
    (.plain starlark%[mark(3, 0)], .plain starlark%[0])])
  (· == .indexRange 1 0) [1, 2, 0, 0, 0, 0, 0, 0]

#guard checkPlacementFailure
  (.dictDisplay [(collect starlark%[mark(1, [])], collect starlark%[mark(2, [9])]),
    (.plain starlark%[mark(3, 0)], .plain starlark%[0])])
  isUnhashableList [1, 2, 0, 0, 0, 0, 0, 0]

-- Display duplicates preserve the accepted prefix in Lean's private
-- accumulator and abort before the next key.
#guard checkPlacementFailure
  (.dictDisplay
    [(lengthOf (collect starlark%[mark(1, [0])]), .plain starlark%[mark(2, 11)]),
     (lengthOf (collect starlark%[mark(3, [0])]), .plain starlark%[mark(4, 22)]),
     (.plain starlark%[mark(5, 2)], .plain starlark%[0])])
  (· == .duplicateKey (intValue 1)) [1, 2, 3, 4, 0, 0, 0, 0]
  (fun before final => final.heap[before.heap.size]?.map Cell.contents ==
    some (.dict [⟨intValue 1, [.scalar (.int 1)], intValue 11⟩]))

-- Indexing validates the receiver after evaluating the subscript.
#guard checkPlacementFailure
  (.index failedArgument (lengthOf (collect starlark%[mark(1, [0])])))
  isUnhashableList [3, 4, 5, 4, 5, 0, 0, 0]

#guard checkPlacementFailure
  (.index (.plain starlark%[mark(1, 0)]) (.plain starlark%[mark(2, [])[1]]))
  (· == .indexRange 1 0) [1, 2, 0, 0, 0, 0, 0, 0]

#guard checkPlacementFailure
  (.index (.plain starlark%[mark(1, 0)]) (collect starlark%[mark(2, [])]))
  (· == .indexTarget) [1, 2, 0, 0, 0, 0, 0, 0]

#guard checkPlacementFailure
  (.index (collect starlark%[mark(1, [0])]) (collect starlark%[mark(2, [])]))
  (· == .indexType) [1, 2, 0, 0, 0, 0, 0, 0]

-- All four positions contain a comprehension. Present operands run once
-- in syntax order even though stride validation happens before bound validation.
#guard
  let result := CompExpr.slice (collect starlark%[mark(1, [0, 1, 2, 3, 4])])
    (some (lengthOf (collect starlark%[mark(2, [0, 0, 0, 0])])))
    (some (lengthOf (collect starlark%[mark(3, [])])))
    (some (.branch (collect starlark%[mark(4, [True])]) (.plain starlark%[-2]) (.plain starlark%[len(1)])))
  let commands := logCommands ++
    [.define "run" {} (.retCompExpr result), .assign "out" starlark%[run()],
     .assign "ok" starlark%[{(4, 2, 2): True}[(out[0], out[1], len(out))]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
      match published.exports.lookup "events" with
      | some (.list address) => eventsMatch state address [1, 2, 3, 4, 0, 0, 0, 0]
      | _ => false
  | _ => false

-- Omitted and explicit None bounds use the same defaults. A written -1
-- under a negative stride is normalized as an integer instead.
#guard
  let reverse := CompExpr.slice (collect starlark%[mark(1, [0, 1, 2])]) none none (some (.plain starlark%[-1]))
  let suffix := CompExpr.slice (.plain starlark%[(3, 4, 5)])
    (some (lengthOf (collect starlark%[mark(2, [0])]))) none none
  let noneBound := CompExpr.branch (collect starlark%[mark(3, [True])]) (.plain starlark%[None])
    (.plain starlark%[len(1)])
  let range := CompExpr.slice (.plain starlark%[range(5)]) none (some noneBound) (some (.plain starlark%[-2]))
  let empty := CompExpr.slice (collect starlark%[mark(4, [0, 1, 2])]) none
    (some (.plain starlark%[-1])) (some (.plain starlark%[-1]))
  let commands := logCommands ++
    [.assignCompExpr "out" (.tupleDisplay [reverse, suffix, range, empty]),
     .assign "ok" starlark%[{(2, 3, 4, 2, 2, 3, 0): True}[
       (out[0][0], len(out[0]), out[1][0], len(out[1]), out[2][1], len(out[2]), len(out[3]))]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
      match published.exports.lookup "events" with
      | some (.list address) => eventsMatch state address [1, 2, 3, 4, 0, 0, 0, 0]
      | _ => false
  | _ => false

-- Trigger a nested comprehension failure at each position in turn.
-- Every later expression is skipped and both active comprehension
-- iterators unwind, leaving the caller's existing guard intact.
#guard
  let start : CompExpr := lengthOf (collect starlark%[mark(2, [])])
  let stop : CompExpr := lengthOf (collect starlark%[mark(6, [])])
  let stride : CompExpr := .plain starlark%[mark(7, 0)]
  let receiver : CompExpr := .plain starlark%[mark(1, 0)]
  checkPlacementFailure (.slice failedArgument (some start) (some stop) (some stride))
      isUnhashableList [3, 4, 5, 4, 5, 0, 0, 0] &&
    checkPlacementFailure (.slice receiver (some failedArgument) (some stop) (some stride))
      isUnhashableList [1, 3, 4, 5, 4, 5, 0, 0] &&
    checkPlacementFailure (.slice receiver (some start) (some failedArgument) (some stride))
      isUnhashableList [1, 2, 3, 4, 5, 4, 5, 0] &&
    checkPlacementFailure (.slice receiver (some start) (some stop) (some failedArgument))
      isUnhashableList [1, 2, 6, 3, 4, 5, 4, 5]

-- Validation starts after every operand succeeds, checking the receiver,
-- stride, start and stop. A zero stride beats either invalid bound.
#guard
  let good := collect starlark%[mark(1, [0, 1])]
  let bad := CompExpr.plain starlark%[mark(1, 0)]
  let start := collect starlark%[mark(2, [])]
  let stop := collect starlark%[mark(3, [])]
  let zero := lengthOf (collect starlark%[mark(4, [])])
  let malformed := collect starlark%[mark(4, [])]
  let negative := CompExpr.plain starlark%[mark(4, -1)]
  let events := [1, 2, 3, 4, 0, 0, 0, 0]
  checkPlacementFailure (.slice bad (some start) (some stop) (some zero)) (· == .sliceTarget) events &&
    checkPlacementFailure (.slice good (some start) (some stop) (some zero)) (· == .zeroSliceStride) events &&
    checkPlacementFailure (.slice good (some start) (some stop) (some malformed))
      (fun | .sliceStrideType (.list _) => true | _ => false) events &&
    checkPlacementFailure (.slice good (some start) (some stop) (some negative))
      (fun | .sliceStartType (.list _) => true | _ => false) events &&
    checkPlacementFailure (.slice good (some (lengthOf start)) (some stop) (some negative))
      (fun | .sliceStopType (.list _) => true | _ => false) events

-- A rejected slice allocates no result or lexical scratch cells.
#guard
  let input := globalSlot "input"
  let destination := globalSlot "out"
  let before : State := { heap := #[⟨.list [intValue 8], false⟩] }
  let before := (before.write input (.list 0)).write destination (intValue 91)
  let omitted := Functions.Comprehensions.Expression.plain (.atom (.scalar .none))
  let expression := Functions.Comprehensions.Expression.slice (.plain (.atom (.read (.bound input))))
    omitted omitted (.plain (.atom (.scalar (.int 0))))
  match Functions.run #[] (expression.body destination) before,
      Functions.run #[] (expression.lower destination) before with
  | .error .zeroSliceStride direct, .error .zeroSliceStride lowered =>
    direct.heap == before.heap && lowered.heap == before.heap &&
      (direct.bindingValue destination).toOption == some (intValue 91) &&
      (lowered.bindingValue destination).toOption == some (intValue 91)
  | _, _ => false

-- Each inner first iterable sees its enclosing x. The outer first
-- iterable captures the function's x, and the later clauses read the
-- comprehension's x. The false first item short-circuits the filter.
#guard
  let first := CompExpr.list ⟨starlark%[x], starlark%[x], .yield starlark%[mark(1, x)]⟩
  let filter := CompExpr.logical .and (.plain starlark%[x])
    (.list ⟨starlark%[x], starlark%[[mark(2, x)]], .yield starlark%[x]⟩)
  let later := CompExpr.list ⟨starlark%[x], starlark%[[mark(3, x)]], .yield starlark%[x]⟩
  let expression := CompExpr.listClauses starlark%[x] first
    (.filter filter (.forIn starlark%[y] later (.yield starlark%[(x, y)])))
  let worker := Statement.define "worker" {}
    (.seq (.assignCompExpr "result" expression) (.ret (some starlark%[(len(x), result)])))
  let commands := logCommands ++
    [.define "run" { positional := [⟨"x", none⟩] } (.seq worker (.ret (some starlark%[worker()]))),
     .assign "out" starlark%[run([0, 4])],
     .assign "ok" starlark%[{(2, 1, 4, 4): True}[(out[0], len(out[1]), out[1][0][0], out[1][0][1])]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
      match published.exports.lookup "events" with
      | some (.list address) => eventsMatch state address [1, 1, 2, 3, 0, 0, 0, 0]
      | _ => false
  | _ => false

-- The dictionary accumulator still overwrites repeated keys in order.
-- A later iterable can itself be a dictionary comprehension.
#guard
  let rows := collect starlark%[[("a", 0), ("a", 1), ("a", 2)]]
  let test := CompExpr.logical .and (.plain starlark%[v]) (collect starlark%[[v]])
  let keys := CompExpr.dict ⟨starlark%[w], starlark%[[v]], .yield (starlark%[w], starlark%[None])⟩
  let expression := CompExpr.dictClauses starlark%[(k, v)] rows
    (.filter test (.forIn starlark%[y] keys (.yield (starlark%[k], starlark%[y]))))
  match runModule [.assignCompExpr "out" expression, .assign "ok" starlark%[{2: True}[out["a"]]]] noImports {} with
  | .ok (.ok published _) => published.exports.lookup "ok" == some (.scalar (.bool true))
  | _ => false

-- Even a later target shadows an enclosing name throughout the block.
-- The nested iterable that looks up z fails only if its filter is reached.
#guard
  let plan := fun input =>
    CompExpr.listClauses starlark%[x] (.plain input)
      (.filter (collect starlark%[z]) (.forIn starlark%[z] (.plain starlark%[[]]) (.yield starlark%[x])))
  let run := fun input => runModule [.assign "z" starlark%[[8]], .assignCompExpr "out" (plan input)] noImports {}
  let unbound := match run starlark%[[1]] with
    | .ok (.error (.runtime (.uninitialized name)) state) => name == fileSlot "z" && state.iterators.isEmpty
    | _ => false
  let skipped := match run starlark%[[]] with
    | .ok (.ok _ state) => state.iterators.isEmpty
    | _ => false
  unbound && skipped

-- Fail before the first cursor, in a filter, or before a later cursor
-- acquisition. The failed inner dictionary retains its operand effects.
#guard
  let expected := [3, 4, 5, 4, 5, 0, 0, 0]
  let rows := CompExpr.plain starlark%[rows]
  checkPlacementFailure (.listClauses starlark%[row] failedArgument (.yield starlark%[row]))
      isUnhashableList expected &&
    checkPlacementFailure (.listClauses starlark%[row] rows
      (.forIn starlark%[item] failedArgument (.yield starlark%[item]))) isUnhashableList expected &&
    checkPlacementFailure (.dictClauses starlark%[row] rows
      (.filter failedArgument (.yield (starlark%[0], starlark%[row])))) isUnhashableList expected

-- Iterating the same list in a nested filter must leave the outer guard
-- active. The next filter fails on mutation and unwinds the outer guard.
#guard
  let expression := CompExpr.listClauses starlark%[row] (.plain starlark%[rows])
    (.filter (collect starlark%[rows]) (.filter (.plain starlark%[touch()]) (.yield starlark%[row])))
  let commands := logCommands ++
    [.assign "rows" starlark%[[[1]]],
     .define "touch" {} (.seq (.eval starlark%[mark(6, 0)])
       (.seq (.setIndex starlark%[rows] starlark%[0] starlark%[[]]) (.ret (some starlark%[True])))),
     .assignCompExpr "out" expression]
  checkAssignmentFailure commands (fun | .activeIteration _ => true | _ => false) [6, 0, 0, 0, 0, 0, 0, 0]
    (fun before final =>
      match before.bindingValue (globalSlot "rows") with
      | .ok (.list address) => before.heap[address]? == final.heap[address]?
      | _ => false)

-- A false filter skips the nested head. Its inner first iterable sees
-- the outer comprehension x, and the enclosing parameter survives.
#guard
  let element := CompExpr.listComprehension starlark%[x] (.plain starlark%[mark(1, [x])])
    (.yield (.plain starlark%[mark(2, x)]))
  let result := CompExpr.listComprehension starlark%[x] (.plain starlark%[x])
    (.filter (.plain starlark%[x]) (.yield element))
  let commands := logCommands ++
    [.define "run" { positional := [⟨"x", none⟩] }
      (.seq (.assignCompExpr "result" result) (.ret (some starlark%[(len(x), result)]))),
     .assign "out" starlark%[run([0, 4, 5])],
     .assign "ok" starlark%[{(3, 2, 4, 5): True}[(out[0], len(out[1]), out[1][0][0], out[1][1][0])]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
      match published.exports.lookup "events" with
      | some (.list address) => eventsMatch state address [1, 2, 1, 2, 0, 0, 0, 0]
      | _ => false
  | _ => false

-- The nested key and value run in order. A repeated comprehension key
-- overwrites its value without moving it in iteration order.
#guard
  let key := lengthOf (collect starlark%[mark(1, width)])
  let value := CompExpr.dictComprehension starlark%[x] (.plain starlark%[mark(2, [n])])
    (.yield (.plain starlark%["n"], .plain starlark%[x]))
  let rows := CompExpr.plain starlark%[[([0], 40), ([0, 0], 50), ([0], 60), ([], 0)]]
  let result := CompExpr.dictComprehension starlark%[(width, n)] rows
    (.filter (.plain starlark%[n]) (.yield (key, value)))
  let commands := logCommands ++
    [.define "run" {} (.retCompExpr result), .assign "out" starlark%[run()],
     .assign "keys" starlark%[list(out)],
     .assign "ok" starlark%[{(1, 2, 60, 50): True}[(keys[0], keys[1], out[1]["n"], out[2]["n"])]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
      match published.exports.lookup "events" with
      | some (.list address) => eventsMatch state address [1, 2, 1, 2, 1, 2, 0, 0]
      | _ => false
  | _ => false

-- A failure in the nested list head or dictionary key releases the
-- nested and enclosing guards. A failed key skips the value entirely.
#guard
  let rows := CompExpr.plain starlark%[rows]
  let expected := [3, 4, 5, 4, 5, 0, 0, 0]
  checkPlacementFailure (.listComprehension starlark%[row] rows (.yield failedArgument))
      isUnhashableList expected &&
    checkPlacementFailure (.dictComprehension starlark%[row] rows
      (.yield (failedArgument, collect starlark%[mark(1, [7])]))) isUnhashableList expected

-- A value error wins over hashability of the already evaluated key.
#guard
  let key := collect starlark%[mark(1, [])]
  let atHead := fun value => CompExpr.dictComprehension starlark%[row] (.plain starlark%[rows])
    (.yield (key, value))
  let value := CompExpr.index (collect starlark%[mark(2, [])]) (.plain starlark%[1])
  let events := [1, 2, 0, 0, 0, 0, 0, 0]
  checkPlacementFailure (atHead value) (· == .indexRange 1 0) events &&
    checkPlacementFailure (atHead (collect starlark%[mark(2, [9])])) isUnhashableList events

-- A failed value for a repeated key retains the earlier pair in the
-- private accumulator. The later item is skipped.
#guard
  let key := lengthOf (collect starlark%[mark(1, [row])])
  let value := CompExpr.branch (.plain starlark%[row]) (collect starlark%[mark(2, [row])])
    (.index (collect starlark%[mark(3, [])]) (.plain starlark%[1]))
  checkPlacementFailure
    (.dictComprehension starlark%[row] (.plain starlark%[[1, 0, 2]]) (.yield (key, value)))
    (· == .indexRange 1 0) [1, 2, 1, 3, 0, 0, 0, 0]
    (fun before final =>
      match final.heap[before.heap.size + 3]?.map Cell.contents with
      | some (.dict [entry]) =>
        entry.key == intValue 1 &&
          match entry.value with
          | .list address => final.heap[address]?.map Cell.contents == some (.list [intValue 1])
          | _ => false
      | _ => false)

-- Completing a nested key over the same list keeps the enclosing
-- guard active while the value tries to mutate the list.
#guard
  let expression := CompExpr.dictComprehension starlark%[row] (.plain starlark%[rows])
    (.yield (lengthOf (collect starlark%[rows]), .plain starlark%[touch()]))
  let commands := logCommands ++
    [.assign "rows" starlark%[[[1]]],
     .define "touch" {} (.seq (.eval starlark%[mark(6, 0)])
       (.seq (.setIndex starlark%[rows] starlark%[0] starlark%[[]]) (.ret (some starlark%[True])))),
     .assignCompExpr "out" expression]
  checkAssignmentFailure commands (fun | .activeIteration _ => true | _ => false) [6, 0, 0, 0, 0, 0, 0, 0]
    (fun before final =>
      match before.bindingValue (globalSlot "rows") with
      | .ok (.list address) => before.heap[address]? == final.heap[address]?
      | _ => false)

-- Each nested head evaluation gets fresh slots even at the same site.
#guard
  let nested := CompExpr.listClauses starlark%[x] (.plain starlark%[source])
    (.filter (.plain starlark%[x or y])
      (.forIn starlark%[y] (.plain starlark%[[2]]) (.yield starlark%[y])))
  let result := CompExpr.listComprehension starlark%[source] (.plain starlark%[[[1], [0]]]) (.yield nested)
  match runModule [.assignCompExpr "out" result] noImports {} with
  | .ok (.error (.runtime (.uninitialized name)) state) => name == fileSlot "y" && state.iterators.isEmpty
  | _ => false

-- All defaults see make's seed, including through the factory's capture.
-- A supplied argument overrides its saved value. Both omitted seeds share
-- the same list, which is frozen through the published closure's defaults.
#guard
  let seed := CompExpr.list ⟨starlark%[x], starlark%[seed], .yield starlark%[mark(2, x)]⟩
  let data := CompExpr.dict ⟨starlark%[x], starlark%[seed], .yield (starlark%[x], starlark%[mark(3, 3)])⟩
  let work := Statement.define "work"
    { positional := [⟨"before", some starlark%[mark(1, seed[0])]⟩, ⟨"seed", some seed⟩],
      keywordOnly := [⟨"data", some data⟩] }
    (.seq (.addIndex starlark%[seed] starlark%[0] starlark%[data[7]])
      (.ret (some starlark%[(before, seed, data)])))
  let factory := Statement.define "factory" {} (.seq work (.ret (some starlark%[work])))
  let commands := logCommands ++
    [.define "make" { positional := [⟨"seed", none⟩] } (.seq factory (.ret (some starlark%[factory()]))),
     .define "use" { positional := [⟨"f", none⟩] }
       (.seq (.assign "a" starlark%[f()]) (.seq (.assign "b" starlark%[f(before=0)])
         (.ret (some starlark%[(a[0], b[0], a[1][0], b[1][0], len(b[2]))])))),
     .assign "f" starlark%[make([7])], .assign "out" starlark%[use(f)],
     .assign "ok" starlark%[{(7, 0, 13, 13, 1): True}[out]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
    match published.exports.lookup "events", published.exports.lookup "f" with
    | some (.list events), some (.function address) =>
      eventsMatch state events [1, 2, 3, 0, 0, 0, 0, 0] &&
      match Functions.getClosure address state with
      | .ok ⟨_, _, [(before, v), (seed, .list xs), (data, .dict dict)]⟩ _ =>
        before == fileSlot "before" && v == intValue 7 &&
          seed == fileSlot "seed" && data == fileSlot "data" &&
          state.heap[xs]?.any Cell.frozen && state.heap[dict]?.any Cell.frozen
      | _ => false
    | _, _ => false
  | _ => false

-- An earlier default and the successful prefix of a failing dictionary
-- comprehension leave effects. Neither a later default nor closure
-- installation runs. Both generated paths keep the prior closure binding.
#guard
  let first := CompExpr.list ⟨starlark%[x], starlark%[mark(1, [40])], .yield starlark%[mark(2, 41)]⟩
  let signature : SourceSignature :=
    { positional := [⟨"xs", some first⟩, ⟨"bad", some failedArgument⟩],
      keywordOnly := [⟨"later", some starlark%[mark(6, 0)]⟩] }
  let commands := logCommands ++
    [.assign "rows" starlark%[[[("a", [4]), ([], [5])]]],
     .define "out" signature .pass]
  match resolve commands with
  | .ok resolved =>
    match resolved.source.commands.reverse with
    | .exec (.defineWithDefaults name id defaults) :: reversed =>
      match runCommands resolved.program noImports reversed.reverse (enter resolved.source {}) with
      | .ok () entered =>
        let target := globalSlot name
        match entered.bindingValue (globalSlot "mark"), entered.bindingValue (globalSlot "rows") with
        | .ok (.function old), .ok (.list outer) =>
          let before := { entered.write target (.function old) with iterators := [outer] }
          let run := fun stages => Functions.run resolved.program
            (Functions.Comprehensions.definitionWithDefaults stages target id defaults) before
          match run Functions.Comprehensions.directStages,
            run (Functions.Comprehensions.loweredStages 0) with
          | .error (.unhashableKey (.list bad)) direct, .error (.unhashableKey (.list bad')) lowered =>
            bad == bad' && direct.heap == lowered.heap &&
            direct.iterators == [outer] && lowered.iterators == [outer] &&
            direct.slots target == before.slots target && lowered.slots target == before.slots target &&
            (direct.bindingValue target).toOption == some (.function old) &&
            (lowered.bindingValue target).toOption == some (.function old) &&
            defaults.all (fun (slot, _) =>
              let saved := Functions.Comprehensions.defaultSlot slot
              (direct.bindings saved).isNone && (lowered.bindings saved).isNone) &&
            direct.heap.any (fun cell => cell.contents == .list [intValue 41]) &&
            direct.heap.all (fun cell => match cell.contents with
              | .function closure => closure.declaration != id
              | _ => true) &&
            match direct.bindingValue (globalSlot "events") with
            | .ok (.list address) => eventsMatch direct address [1, 2, 3, 4, 5, 4, 5, 0]
            | _ => false
          | _, _ => false
        | _, _ => false
      | _ => false
    | _ => false
  | _ => false

-- Validation reaches a default's skipped code even for an uncalled function.
#guard
  let duplicate := CompExpr.call (.plain starlark%[len]) []
    [("x", .plain starlark%[1]), ("x", collect starlark%[[]])] none none
  let value := CompExpr.branch (.plain starlark%[True]) (.plain starlark%[0]) duplicate
  match resolve [.define "unused" { positional := [⟨"value", some value⟩] } .pass] with
  | .error (.validation (.syntax (.duplicateExplicitKeyword "x"))) => true
  | _ => false

-- The nested head's locals start uninitialized on its second visit.
#guard
  let inner := CompExpr.listClauses starlark%[x] (.plain starlark%[source])
    (.filter (.plain starlark%[x or y])
      (.forIn starlark%[y] (.plain starlark%[[2]]) (.yield starlark%[y])))
  let value := CompExpr.listComprehension starlark%[source] (.plain starlark%[[[1], [0]]]) (.yield inner)
  match runModule [.define "unused" { positional := [⟨"value", some value⟩] } .pass] noImports {} with
  | .ok (.error (.runtime (.uninitialized name)) state) => name == fileSlot "y" && state.iterators.isEmpty
  | _ => false

-- A function's RHS sees the old parameter before either repeated name
-- is written. A module pattern uses the same binder and publishes its
-- public leaves only.
#guard
  let localRhs := CompExpr.list
    ⟨starlark%[piece], starlark%[mark(1, [8, [9, x]])], .yield starlark%[mark(2, piece)]⟩
  let moduleRhs := CompExpr.list
    ⟨starlark%[piece], starlark%[mark(3, [[7], (2, 3)])], .yield starlark%[mark(4, piece)]⟩
  let commands := logCommands ++
    [.define "f" { positional := [⟨"x", none⟩] }
       (.seq (.assignTargetCompExpr starlark%[(x, [x, y])] localRhs)
         (.ret (some starlark%[(x, y)]))),
     .assign "out" starlark%[f(4)],
     .assignTargetCompExpr starlark%[(payload, [countValue, _hidden])] moduleRhs,
     .assign "ok" starlark%[{((9, 4), 7, 2): True}[(out, payload[0], countValue)]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
    (published.exports.lookup "_hidden").isNone &&
    match published.exports.lookup "events" with
    | some (.list address) => eventsMatch state address [1, 2, 2, 3, 4, 4, 0, 0]
    | _ => false
  | _ => false

private def checkPatternRhsFailure (failRhs : Bool) : Bool :=
  let rows := if failRhs then starlark%[[[(False, 5), (True, [6]), (False, 7)]]]
    else starlark%[[[(False, 5), (False, [6]), (False, 7)]]]
  let rhs := CompExpr.list ⟨starlark%[row], starlark%[mark(1, rows)],
    .forIn starlark%[(fail, x)] starlark%[row]
      (.yield starlark%[mark(3, [])[1] if fail else mark(2, x)])⟩
  let commands := logCommands ++ [.assign "rows" rows,
    .assignTargetCompExpr starlark%[(a, [b, c], d)] rhs]
  match resolve commands with
  | .ok resolved =>
    match resolved.source.commands.reverse with
    | .exec (.assignTargetCompExpr target expr) :: reversed =>
      match runCommands resolved.program noImports reversed.reverse (enter resolved.source {}) with
      | .ok () entered =>
        match entered.bindingValue (globalSlot "rows") with
        | .ok (.list outer) =>
          let a := globalSlot "a"
          let names := [a, globalSlot "b", globalSlot "c", globalSlot "d"]
          let saved := Functions.Comprehensions.expressionSlot
          -- An unowned first leaf tests that restoring the RHS frame
          -- does not discard the binder's direct writes.
          let start := { entered with
            slots := fun name => if name = a then none else entered.slots name
            iterators := [outer] }
          let before := (names.zip ([90, 91, 92, 93].map intValue)).foldl
            (fun state (name, value) => state.write name value) (start.write saved (intValue 94))
          let run := fun stages => Functions.run resolved.program (expr.assignTargetCode target stages) before
          match run Functions.Comprehensions.directStages, run (Functions.Comprehensions.loweredStages 0) with
          | .error first direct, .error second lowered =>
            let expectedError := if failRhs then Lists.Error.indexRange 1 0 else .unpackArity 2 1
            let expected := (if failRhs then [90, 91, 92, 93] else [5, 91, 92, 93]).map (some ∘ intValue)
            let written := fun (state : State) => names.map fun name => (state.bindingValue name).toOption
            first == expectedError && second == first &&
              direct.heap == lowered.heap && direct.iterators == [outer] && lowered.iterators == [outer] &&
              written direct == expected && written lowered == expected &&
              direct.bindings saved == some (intValue 94) && lowered.bindings saved == some (intValue 94) &&
              match direct.bindingValue (globalSlot "events") with
              | .ok (.list address) =>
                eventsMatch direct address (if failRhs then [1, 2, 3, 0, 0, 0, 0, 0] else [1, 2, 2, 2, 0, 0, 0, 0])
              | _ => false
          | _, _ => false
        | _ => false
      | _ => false
    | _ => false
  | _ => false

#guard checkPatternRhsFailure false && checkPatternRhsFailure true

-- Scope collection visits the target before analyzing the lexical block.
-- Reading its global before the assignment is a runtime unbound error.
#guard
  match runModule [.assign "out" starlark%[a],
    .assignTargetCompExpr starlark%[(a, b)] (collect starlark%[[1, 2]])] noImports {} with
  | .ok (.error (.runtime (.uninitialized name)) _) => name == globalSlot "a"
  | _ => false

-- Target shape checking also runs in a branch that won't execute.
#guard
  let invalid := Statement.assignTargetCompExpr starlark%[(a, [b, rows[:]])] (collect starlark%[[]])
  match resolve [.define "f" {} (.branch starlark%[False] invalid .pass)] with
  | .error .unsupportedAssignmentTarget => true
  | _ => false

private def fromComprehension (iterable : Functions.Lowering.Resolve.SourceExpr) : CompExpr :=
  .index (collect iterable) (.plain starlark%[0])

private def sameAliasReceiver : CompExpr :=
  .index (.list ⟨starlark%[x], starlark%[alias], .yield starlark%[mark(2, alias)]⟩) (.plain starlark%[0])

-- Each input runs once, including the receiver comprehension over its
-- own target. The dictionary write sees the key added by the index operand.
#guard
  let arrayWrite := Statement.setIndexCompExpr sameAliasReceiver (fromComprehension starlark%[[mark(3, -1)]])
    (fromComprehension starlark%[[mark(1, 9)]])
  let index := CompExpr.index (.dict ⟨starlark%[x], starlark%[[0]],
    .yield (starlark%[x], starlark%[choose()])⟩) (.plain starlark%[0])
  let commands := logCommands ++
    [.assign "target" starlark%[[7]], .assign "alias" starlark%[target],
     .define "change" {} arrayWrite, .eval starlark%[change()],
     .assign "table" starlark%[{"b": 7, "a": 8}], .assign "twin" starlark%[table],
     .define "choose" {} (.seq (.setIndex starlark%[table] starlark%["c"] starlark%[11])
       (.ret (some starlark%[mark(6, "b")]))),
     .setIndexCompExpr (fromComprehension starlark%[[mark(5, twin)]]) index
       (fromComprehension starlark%[[mark(4, 10)]]),
     .setIndexCompExpr (.plain starlark%[twin]) (fromComprehension starlark%[["d"]]) (.plain starlark%[12]),
     .assign "keys" starlark%[list(table)],
     .assign "ok" starlark%[{(9, 10, 11, 12, "b", "a", "c", "d"): True}[
       (target[0], table["b"], table["c"], table["d"], keys[0], keys[1], keys[2], keys[3])]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
    published.exports.lookup "target" == published.exports.lookup "alias" &&
    published.exports.lookup "table" == published.exports.lookup "twin" &&
    match published.exports.lookup "events" with
    | some (.list address) => eventsMatch state address [1, 2, 3, 4, 5, 6, 0, 0]
    | _ => false
  | _ => false

private def brokenStoreOperand (iterable : Functions.Lowering.Resolve.SourceExpr) : CompExpr :=
  .list ⟨starlark%[row], iterable, .forIn starlark%[x] starlark%[row] (.yield starlark%[[][0]])⟩

private def checkStoreFailure (targetValue : Functions.Lowering.Resolve.SourceExpr) (store : Command)
    (expectedError : Address → Lists.Error → Bool) (trace : List Int)
    (prepare : Address → State → State := fun _ state => state) : Bool :=
  let commands := logCommands ++ [.assign "target" targetValue, .assign "alias" starlark%[target],
    .assign "rows" starlark%[[[0]]], store]
  match resolve commands with
  | .ok resolved =>
    match resolved.source.commands.reverse with
    | .exec code :: reversed =>
      let staged := match code with
        | .setIndexCompExpr recv index value => some (Functions.Comprehensions.setIndexCode recv index value)
        | .addIndexCompExpr recv index value => some (Functions.Comprehensions.addIndexCode recv index value)
        | _ => none
      match staged, runCommands resolved.program noImports reversed.reverse (enter resolved.source {}) with
      | some emit, .ok () entered =>
        match entered.bindingValue (globalSlot "target"), entered.bindingValue (globalSlot "rows") with
        | .ok (.list address), .ok (.list rows) | .ok (.dict address), .ok (.list rows) =>
          let saved := List.range 4 |>.map Functions.Comprehensions.argumentSlot
          let before := prepare address ({ entered with iterators := [rows] })
          let before := saved.foldl (fun state slot => state.write slot (intValue 93)) before
          let run := fun stages => Functions.run resolved.program (emit stages) before
          match run Functions.Comprehensions.directStages, run (Functions.Comprehensions.loweredStages 0) with
          | .error first direct, .error second lowered =>
            expectedError address first && second == first && direct.heap == lowered.heap &&
            direct.heap[address]? == before.heap[address]? &&
            direct.iterators == before.iterators && lowered.iterators == before.iterators &&
            saved.all (fun slot => direct.bindings slot == before.bindings slot &&
              lowered.bindings slot == before.bindings slot) &&
            match direct.bindingValue (globalSlot "events") with
            | .ok (.list events) => eventsMatch direct events (trace ++ List.replicate (8 - trace.length) 0)
            | _ => false
          | _, _ => false
        | _, _ => false
      | _, _ => false
    | _ => false
  | _ => false

#guard
  let rhs := fromComprehension starlark%[[mark(1, 9)]]
  let recv := fromComprehension starlark%[[mark(2, alias)]]
  let index := fromComprehension starlark%[[mark(3, 0)]]
  let invalid := fromComprehension starlark%[[mark(2, 7)]]
  let atIndex := fun _ error => error == .indexRange 0 0
  checkStoreFailure starlark%[[7]]
    (.setIndexCompExpr recv index (brokenStoreOperand starlark%[mark(1, rows)])) atIndex [1] &&
  checkStoreFailure starlark%[[7]]
    (.setIndexCompExpr (brokenStoreOperand starlark%[mark(2, rows)]) index rhs) atIndex [1, 2] &&
  checkStoreFailure starlark%[[7]]
    (.setIndexCompExpr invalid (brokenStoreOperand starlark%[mark(3, rows)]) rhs) atIndex [1, 2, 3] &&
  checkStoreFailure starlark%[[7]] (.setIndexCompExpr invalid index rhs)
    (fun _ error => error == .assignmentTarget) [1, 2, 3]

#guard
  let rhs := fromComprehension starlark%[[mark(1, 9)]]
  let recv := fromComprehension starlark%[[mark(2, alias)]]
  let index := fromComprehension starlark%[[mark(3, 0)]]
  let badKey := fromComprehension starlark%[[mark(3, [])]]
  let freezeList := fun address (state : State) => state.freeze [.list address]
  checkStoreFailure starlark%[[7]] (.setIndexCompExpr recv (fromComprehension starlark%[[mark(3, 2)]]) rhs)
    (fun _ error => error == .indexRange 2 1) [1, 2, 3] freezeList &&
  checkStoreFailure starlark%[{"b": 7}] (.setIndexCompExpr recv badKey rhs)
    (fun _ => isUnhashableList) [1, 2, 3] &&
  checkStoreFailure starlark%[{"b": 7}] (.setIndexCompExpr recv badKey rhs) (fun address error => error == .frozen address)
    [1, 2, 3] (fun address state => state.freeze [.dict address]) &&
  checkStoreFailure starlark%[[7]] (.setIndexCompExpr sameAliasReceiver index rhs)
    (fun address error => error == .activeIteration address)
    [1, 2, 3] (fun address state => { state with iterators := address :: state.iterators })

-- The RHS changes both a saved list and the receiver selection. The
-- write still uses the old integer and the original object. The same
-- integer addition works for a dictionary element and a lexical name.
#guard
  let commands := logCommands ++
    [.assign "first" starlark%[[7]], .assign "second" starlark%[[50]],
     .assign "alias" starlark%[first], .assign "selected" starlark%[[alias]],
     .define "change" {} (.seq (.setIndex starlark%[selected] starlark%[0] starlark%[second])
       (.seq (.setIndex starlark%[alias] starlark%[0] starlark%[100]) (.ret (some starlark%[mark(3, 2)])))),
     .define "update" {} (.addIndexCompExpr (fromComprehension starlark%[[mark(1, selected[0])]])
       (fromComprehension starlark%[[mark(2, -1)]]) (fromComprehension starlark%[[change()]])),
     .eval starlark%[update()],
     .assign "table" starlark%[{"b": 7, "a": 8}], .assign "twin" starlark%[table],
     .addIndexCompExpr (fromComprehension starlark%[[mark(4, twin)]])
       (fromComprehension starlark%[[mark(5, "b")]]) (fromComprehension starlark%[[mark(6, 9)]]),
     .define "bump" { positional := [⟨"x", none⟩] }
       (.seq (.addNameCompExpr "x" (fromComprehension starlark%[[mark(7, x)]])) (.ret (some starlark%[x]))),
     .assign "keys" starlark%[list(table)],
     .assign "ok" starlark%[{(9, 9, 50, 50, 16, "b", 6): True}[
       (first[0], alias[0], second[0], selected[0][0], table["b"], keys[0], bump(3))]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
    published.exports.lookup "table" == published.exports.lookup "twin" &&
    match published.exports.lookup "events" with
    | some (.list address) => eventsMatch state address [1, 2, 3, 4, 5, 6, 7, 0]
    | _ => false
  | _ => false

-- Plain assignment inserts the key and evaluates the RHS first.
-- Augmented assignment needs an old value at that key before the RHS.
#guard
  let receiver := fromComprehension starlark%[[mark(1, alias)]]
  let index := fromComprehension starlark%[[mark(2, "new")]]
  let rhs := fromComprehension starlark%[[mark(3, 9)]]
  let commands := logCommands ++ [.assign "target" starlark%[{"b": 7}], .assign "alias" starlark%[target],
    .setIndexCompExpr receiver index rhs, .assign "out" starlark%[target["new"]]]
  let plain := match runModule commands noImports {} with
    | .ok (.ok published state) =>
      published.exports.lookup "out" == some (intValue 9) &&
      match published.exports.lookup "events" with
      | some (.list address) => eventsMatch state address [3, 1, 2, 0, 0, 0, 0, 0]
      | _ => false
    | _ => false
  plain && checkStoreFailure starlark%[{"b": 7}] (.addIndexCompExpr receiver index rhs)
    (fun _ error => error == .missingKey (.string "new")) [1, 2]

#guard
  let receiver := fromComprehension starlark%[[mark(1, alias)]]
  let index := fromComprehension starlark%[[mark(2, 0)]]
  let rhs := fromComprehension starlark%[[mark(3, 9)]]
  let brokenAt := fun _ error => error == .indexRange 0 0
  let check := checkStoreFailure starlark%[[7]]
  check (.addIndexCompExpr (brokenStoreOperand starlark%[mark(1, rows)]) index rhs) brokenAt [1] &&
  check (.addIndexCompExpr receiver (brokenStoreOperand starlark%[mark(2, rows)]) rhs) brokenAt [1, 2] &&
  check (.addIndexCompExpr receiver (fromComprehension starlark%[[mark(2, 2)]]) rhs)
    (fun _ error => error == .indexRange 2 1) [1, 2] &&
  check (.addIndexCompExpr receiver index (brokenStoreOperand starlark%[mark(3, rows)])) brokenAt [1, 2, 3]

#guard
  let receiver := fromComprehension starlark%[[mark(1, alias)]]
  let index := fromComprehension starlark%[[mark(2, 0)]]
  let rhs := fromComprehension starlark%[[mark(3, 9)]]
  let bad := fromComprehension starlark%[[mark(3, True)]]
  let iterateAlias := CompExpr.index
    (.list ⟨starlark%[x], starlark%[alias], .yield starlark%[mark(1, alias)]⟩) (.plain starlark%[0])
  let check := fun store error trace prepare =>
    checkStoreFailure starlark%[[7]] store error trace prepare
  check (.addIndexCompExpr receiver index bad)
    (fun _ error => error == .integerAddType (intValue 7) (.scalar (.bool true))) [1, 2, 3]
    (fun address state => state.freeze [.list address]) &&
  check (.addIndexCompExpr receiver index rhs) (fun address error => error == .frozen address)
    [1, 2, 3] (fun address state => state.freeze [.list address]) &&
  check (.addIndexCompExpr iterateAlias index rhs) (fun address error => error == .activeIteration address)
    [1, 2, 3] (fun address state => { state with iterators := address :: state.iterators })

-- Failure inside a nested RHS comprehension keeps its own write
-- through an alias. The augmented write-back and later code are skipped.
#guard
  let commands := logCommands ++
    [.assign "target" starlark%[[7]], .assign "alias" starlark%[target], .assign "rows" starlark%[[[0]]],
     .define "change" {} (.seq (.setIndex starlark%[alias] starlark%[0] starlark%[100])
       (.ret (some starlark%[mark(3, rows)]))),
     .addIndexCompExpr (fromComprehension starlark%[[mark(1, alias)]])
       (fromComprehension starlark%[[mark(2, 0)]]) (brokenStoreOperand starlark%[change()]),
     .eval starlark%[mark(99, 0)]]
  match runModule commands noImports {} with
  | .ok (.error (.runtime (.indexRange 0 0)) state) =>
    state.heap.any (·.contents == .list [intValue 100]) &&
    state.heap.any (·.contents == .list ([1, 2, 3, 0, 0, 0, 0, 0].map intValue))
  | _ => false

-- A name target itself establishes a local, so its old value is unbound.
#guard
  let commands := logCommands ++
    [.assign "x" starlark%[7],
     .define "f" {} (.addNameCompExpr "x" (fromComprehension starlark%[[mark(1, 9)]])),
     .eval starlark%[f()]]
  match runModule commands noImports {} with
  | .ok (.error (.runtime (.uninitialized name)) state) =>
    name == fileSlot "x" && state.heap.any (·.contents == .list (List.replicate 8 (intValue 0)))
  | _ => false

-- The first name is visible to the later receiver. The nested module
-- pattern reads its second child from the unpack snapshot after writing
-- through an alias of that same sequence.
#guard
  let localTarget := starlark%[(x, [mark(2, x)[mark(3, 0)], table[mark(4, "new")]])]
  let moduleTarget := starlark%[([mark(6, row)[mark(7, 1)], saved], out)]
  let commands := logCommands ++
    [.assign "alias" starlark%[[7]], .assign "table" starlark%[{"old": 8}],
     .define "f" { positional := [⟨"x", none⟩] }
       (.seq (.assignTargetCompExpr localTarget (collect starlark%[mark(1, [alias, [9, 10]])]))
         (.ret (some starlark%[x[0]]))),
     .assign "result" starlark%[f(None)], .assign "row" starlark%[[10, 20]],
     .assignTargetCompExpr moduleTarget (collect starlark%[mark(5, [row, 12])]),
     .assign "ok" starlark%[{(9, 9, 10, 10, 20, 12): True}[
       (result, alias[0], table["new"], row[1], saved, out)]]]
  match runModule commands noImports {} with
  | .ok (.ok published state) =>
    published.exports.lookup "ok" == some (.scalar (.bool true)) &&
    match published.exports.lookup "events" with
    | some (.list events) => eventsMatch state events [1, 2, 3, 4, 5, 6, 7, 0]
    | _ => false
  | _ => false

private def checkMixedPatternFailure (target : Functions.Lowering.Resolve.SourceExpr) (rhs : CompExpr)
    (error : Lists.Error) (names : List Int) (afterStore : Int) (trace : List Int) : Bool :=
  let commands := logCommands ++ [.assign "xs" starlark%[[7]], .assign "alias" starlark%[xs],
    .assign "rows" starlark%[[[0]]], .assignTargetCompExpr target rhs]
  match resolve commands with
  | .ok resolved =>
    match resolved.source.commands.reverse with
    | .exec (.assignPatternCompExpr target rhs) :: reversed =>
      match runCommands resolved.program noImports reversed.reverse (enter resolved.source {}) with
      | .ok () entered =>
        match entered.bindingValue (globalSlot "rows"), entered.bindingValue (globalSlot "xs") with
        | .ok (.list rows), .ok (.list address) =>
          let a := globalSlot "a"
          let b := globalSlot "b"
          let saved := List.range 3 |>.map (fun depth => Functions.Comprehensions.patternSlot depth 0)
          let allocated := Functions.Comprehensions.patternSlot 1 0
          let entered := entered.allocateSlot allocated
          let start := { entered with
            slots := fun key => if key = a then none else entered.slots key
            iterators := [rows] }
          let before := saved.foldl (fun state slot => state.write slot (intValue 79))
            ((start.write a (intValue 90)).write b (intValue 91))
          let run := fun stages => Functions.run resolved.program
            (Functions.Comprehensions.assignPatternCode target rhs stages) before
          let kept := fun (state : State) =>
            let bindings := [a, b].map fun slot => (state.bindingValue slot).toOption
            bindings == names.map (some ∘ intValue) && state.iterators == [rows] &&
              saved.all (fun slot => decide (state.slots slot = before.slots slot) &&
                (state.bindingValue slot).toOption == some (intValue 79)) &&
              state.heap[address]?.map Cell.contents == some (.list [intValue afterStore])
          match run Functions.Comprehensions.directStages, run (Functions.Comprehensions.loweredStages 0) with
          | .error first direct, .error second lowered =>
            first == error && second == first && direct.heap == lowered.heap && kept direct && kept lowered &&
            match direct.bindingValue (globalSlot "events") with
            | .ok (.list events) => eventsMatch direct events (trace ++ List.replicate (8 - trace.length) 0)
            | _ => false
          | _, _ => false
        | _, _ => false
      | _ => false
    | _ => false
  | _ => false

-- The root RHS, the second unpack, and the later store can each stop
-- the assignment. In the late cases the earlier name and alias writes survive.
#guard
  let target := starlark%[(a, mark(2, alias)[mark(3, 0)], [b, mark(4, alias)[mark(5, 8)]],
    mark(6, alias)[mark(7, 0)])]
  let good := collect starlark%[mark(1, [5, 9, [10, 11], 12])]
  let short := collect starlark%[mark(1, [5, 9, [10], 12])]
  let bad := brokenStoreOperand starlark%[mark(1, rows)]
  let badReceiver := starlark%[(a, mark(2, alias)[mark(3, 0)], [b, mark(4, [])[0][mark(5, 8)]],
    mark(6, alias)[mark(7, 0)])]
  checkMixedPatternFailure target bad (.indexRange 0 0) [90, 91] 7 [1] &&
  checkMixedPatternFailure target short (.unpackArity 2 1) [5, 91] 9 [1, 2, 3] &&
  checkMixedPatternFailure target good (.indexRange 8 1) [5, 10] 9 [1, 2, 3, 4, 5] &&
  checkMixedPatternFailure badReceiver good (.indexRange 0 0) [5, 10] 9 [1, 2, 3, 4]

-- A receiver read does not add a module binding. Name leaves still
-- participate in the usual single-binding validation.
#guard
  let commands := [.assign "xs" starlark%[[7]],
    .assignTargetCompExpr starlark%[(a, [a, xs[0]])] (collect starlark%[[5, [6, 7]]])]
  match resolve commands with
  | .error (.validation (.bindingCollision "a")) => true
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve

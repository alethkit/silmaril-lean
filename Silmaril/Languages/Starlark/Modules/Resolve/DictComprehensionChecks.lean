module

import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Languages.Starlark.Functions.Comprehensions.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs
meta import Silmaril.Languages.Starlark.Functions.Comprehensions.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve

open scoped Functions.Lowering.Quote
open Lists

private def noImports : Catalog := fun _ => none

private def intValue (value : Int) : Lists.Value := .scalar (.int value)

-- The first operand reads the parameter before the target shadows it.
-- Later clauses use the new block and repeated leaves update the same slot.
#guard
  let comp : DictComp := ⟨starlark%[(x, [x, ys])], starlark%[x],
    .filter starlark%[x] (.forIn starlark%[[k, [v]]] starlark%[ys]
      (.yield (starlark%[k], starlark%[(x, v)])))⟩
  let commands : List Command :=
    [.define "run" { positional := [⟨"x", none⟩] }
      (.seq (.assignDictComp "result" comp) (.ret (some starlark%[(len(x), result["a"])]))),
     .assign "out" starlark%[run([(8, [0, 9]), (9, [7, [("a", [4])]])])],
     .assign "ok" starlark%[{(2, (7, 4)): True}[out]]]
  match runModule commands noImports {} with
  | .ok (.ok published _) => published.exports.lookup "ok" == some (.scalar (.bool true))
  | _ => false

#guard
  let comp : DictComp := ⟨starlark%[(x, [y])], starlark%[[]], .yield (starlark%[x], starlark%[y])⟩
  match resolve [.assignDictComp "out" comp, .eval starlark%[y]] with
  | .error (.expression (.lexical (.undefinedName "y"))) => true
  | _ => false

-- Each visit to the site gets fresh slots, including for dictionary yields.
#guard
  let comp : DictComp := ⟨starlark%[x], starlark%[source],
    .filter starlark%[x or y] (.forIn starlark%[y] starlark%[[2]] (.yield (starlark%[y], starlark%[x])))⟩
  let commands : List Command :=
    [.define "run" {} (.forIn "source" starlark%[[[1], [0]]] (.assignDictComp "result" comp)),
     .eval starlark%[run()]]
  match runModule commands noImports {} with
  | .ok (.error (.runtime (.uninitialized binding)) state) =>
    binding == fileSlot "y" && state.iterators.isEmpty
  | _ => false

private def mark : Command :=
  .define "mark" { positional := [⟨"tag", none⟩, ⟨"value", none⟩] }
    (.seq (.setIndex starlark%[events] starlark%[count[0]] starlark%[tag])
      (.seq (.addIndex starlark%[count] starlark%[0] starlark%[1]) (.ret (some starlark%[value]))))

private def commands (rows key value : Functions.Lowering.Resolve.SourceExpr) : List Command :=
  [.assign "rows" rows, .assign "events" starlark%[[0, 0, 0, 0, 0, 0, 0]],
   .assign "count" starlark%[[0]], mark,
   .assignDictComp "out" ⟨starlark%[row], starlark%[mark(9, rows)],
     .forIn starlark%[(k, [v])] starlark%[row] (.filter starlark%[v] (.yield (key, value)))⟩]

private def elements (state : State) (name : String) : Option (List Lists.Value) :=
  match state.bindingValue (globalSlot name) with
  | .ok (.list address) =>
    match state.heap[address]?.map Cell.contents with
    | some (.list values) => some values
    | _ => none
  | _ => none

private def entries (state : State) (address : Address) : Option (List (Lists.Value × Lists.Value)) := do
  let cell ← state.heap[address]?
  match cell.contents with
  | .dict items => some (items.map fun item => (item.key, item.value))
  | _ => none

private def successCommands := commands starlark%[[[("a", [1]), ("b", [2]), ("a", [3]), ("c", [0])]]]
  starlark%[mark(1, k)] starlark%[mark(2, v)]

-- A module publishes a frozen result. Replacing "a" changes its value
-- in place, and the filtered row never evaluates either operand.
#guard
  match runModule successCommands noImports {} with
  | .ok (.ok published state) =>
    match published.exports.lookup "out" with
    | some (.dict address) => (state.heap[address]?.map Cell.frozen).getD false &&
      entries state address == some [(.string "a", intValue 3), (.string "b", intValue 2)] &&
      match published.exports.lookup "events" with
      | some (.list log) => state.heap[log]?.map Cell.contents == some (.list ([9, 1, 2, 1, 2, 1, 2].map intValue))
      | _ => false
    | _ => false
  | _ => false

private def checkBoth (input : List Command) (check : Address → State → Bool)
    (expectedError : Option (Lists.Error → Bool) := none) : Bool :=
  match resolve input with
  | .ok resolved =>
    match resolved.source.commands.reverse with
    | .exec (.assignDictComp destination comp) :: reversed =>
      match runCommands resolved.program noImports reversed.reverse (enter resolved.source {}) with
      | .ok () entered =>
        let target := globalSlot destination
        let scratch := Functions.Lowering.temporary 0
        let seeded := (entered.write target (intValue 99)).write scratch (intValue 71)
        let guard := seeded.heap.size
        let before := { seeded with heap := seeded.heap.push ⟨.list [], false⟩, iterators := [guard] }
        let run := Functions.denoteBody resolved.program (List.range resolved.program.size)
        let same := fun (direct lowered : State) =>
          direct.heap == lowered.heap && direct.iterators == [guard] && lowered.iterators == [guard] &&
            (lowered.bindingValue scratch).toOption == some (intValue 71) &&
            (direct.bindingValue target).toOption == (lowered.bindingValue target).toOption &&
            direct.slots Functions.Comprehensions.keySlot == none &&
            lowered.slots Functions.Comprehensions.keySlot == none
        let dictionary := before.heap.size + 3
        match run (comp.body target) before, run (comp.lower target) before with
        | .ok .next direct, .ok .next lowered =>
          expectedError.isNone && same direct lowered && check dictionary direct &&
            (direct.bindingValue target).toOption == some (.dict dictionary)
        | .error err direct, .error loweredErr lowered =>
          (expectedError.map (· err)).getD false && err == loweredErr && same direct lowered &&
            check dictionary direct && (direct.bindingValue target).toOption == some (intValue 99)
        | _, _ => false
      | _ => false
    | _ => false
  | _ => false

#guard checkBoth successCommands fun address state =>
  entries state address == some [(.string "a", intValue 3), (.string "b", intValue 2)] &&
    elements state "events" == some ([9, 1, 2, 1, 2, 1, 2].map intValue)

private def failedRows := starlark%[[[("a", [1]), ([], [2]), ("b", [3])]]]

private def checkFailure (key value : Functions.Lowering.Resolve.SourceExpr)
    (log : List Int) (error : Lists.Error → Bool) : Bool :=
  checkBoth (commands failedRows key value) (fun address state =>
    entries state address == some [(.string "a", intValue 1)] &&
      elements state "events" == some (log.map intValue)) (some error)

-- A key expression error skips the value expression entirely.
#guard checkFailure starlark%[mark(1, k) if k else mark(1, k)[1]] starlark%[mark(2, v)]
  [9, 1, 2, 1, 0, 0, 0] (· == .indexRange 1 0)

-- A value expression error wins over hashability of the computed key.
#guard checkFailure starlark%[mark(1, k)] starlark%[mark(2, v) if k else mark(2, v)[0]]
  [9, 1, 2, 1, 2, 0, 0] (· == .indexTarget)

-- Hashability is checked after both effects and before any later pair.
#guard checkFailure starlark%[mark(1, k)] starlark%[mark(2, v)]
  [9, 1, 2, 1, 2, 0, 0] (fun | .unhashableKey (.list _) => true | _ => false)

end Silmaril.Languages.Starlark.Modules.Resolve

module

import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Languages.Starlark.Functions.Comprehensions.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Defs
meta import Silmaril.Languages.Starlark.Functions.Comprehensions.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve

open scoped Functions.Lowering.Quote
open Lists

private def noImports : Catalog := fun _ => none

-- The outer iterable reads the parameter despite the target shadowing it.
-- Each repeated name updates the same slot. Filters and later targets can
-- see the assigned names, but the enclosing function sees its parameter.
#guard
  let comp : ListComp := ⟨starlark%[(x, [x, y])], starlark%[x],
    .filter starlark%[x] (.forIn starlark%[[z, (w, z)]] starlark%[y]
      (.filter starlark%[w] (.yield starlark%[(x, z)])))⟩
  let commands : List Command :=
    [.define "run" { positional := [⟨"x", none⟩] }
      (.seq (.assignListComp "result" comp) (.ret (some starlark%[(len(x), result)]))),
     .assign "out" starlark%[run([(10, [0, 19]), (20, [3, [(5, (0, 9)), (6, (1, 8))]])])],
     .assign "ok" starlark%[{(2, 1, 3, 8): True}[(out[0], len(out[1]), out[1][0][0], out[1][0][1])]]]
  match runModule commands noImports {} with
  | .ok (.ok published _) => published.exports.lookup "ok" == some (.scalar (.bool true))
  | _ => false

-- Forward reads in later operands resolve to the comprehension slot, even
-- when that slot is still uninitialized and an outer name is available.
#guard
  let comp : ListComp := ⟨starlark%[x], starlark%[[1]],
    .forIn starlark%[y] starlark%[z] (.forIn starlark%[z] starlark%[[]] (.yield starlark%[x]))⟩
  match runModule [.assign "z" starlark%[[8]], .assignListComp "out" comp] noImports {} with
  | .ok (.error (.runtime (.uninitialized binding)) _) => binding == fileSlot "z"
  | _ => false

-- A comprehension local does not contribute a name to the enclosing block.
#guard
  let comp : ListComp := ⟨starlark%[(x, [y])], starlark%[[]], .yield starlark%[y]⟩
  match resolve [.assignListComp "out" comp, .eval starlark%[y]] with
  | .error (.expression (.lexical (.undefinedName "y"))) => true
  | _ => false

#guard
  let rejected := fun target =>
    match resolve [.define "run" {} (.branch starlark%[False]
      (.assignListComp "out" ⟨starlark%[x], starlark%[[]],
        .forIn target starlark%[[]] (.yield starlark%[x])⟩) .pass)] with
    | .error .unsupportedComprehensionTarget => true
    | _ => false
  rejected starlark%[[x, (y, xs[0])]] && rejected starlark%[(x, [y, 3])]

-- Exact correspondence on a successful module command and a nested mismatch.
-- The first iterable runs once; the first yield writes an observable effect.
-- On failure the second row's a write survives, b and c keep the old values,
-- the old destination remains visible, and both acquired guards are released.
private def withRows (rows : Functions.Lowering.Resolve.SourceExpr) (fails : Bool) : Bool :=
  let comp : ListComp := ⟨starlark%[row], starlark%[start()],
    .filter starlark%[row] (.forIn starlark%[(a, [b, c])] starlark%[row] (.yield starlark%[observe(a)]))⟩
  let commands : List Command :=
    [.assign "rows" rows, .assign "effects" starlark%[[0, 0]],
     .define "start" {} (.seq (.addIndex starlark%[effects] starlark%[0] starlark%[1])
       (.ret (some starlark%[rows]))),
     .define "observe" { positional := [⟨"x", none⟩] }
       (.seq (.setIndex starlark%[effects] starlark%[1] starlark%[x]) (.ret (some starlark%[x]))),
     .assignListComp "out" comp]
  match resolve commands with
  | .ok resolved =>
    match resolved.source.commands.reverse with
    | .exec (.assignListComp destination resolvedComp) :: reversed =>
      match runCommands resolved.program noImports reversed.reverse (enter resolved.source {}) with
      | .ok () entered =>
        let available := List.range resolved.program.size
        let target := globalSlot destination
        let scratch := Functions.Lowering.temporary 0
        let seeded := (entered.write target (.scalar (.int 99))).write scratch (.scalar (.int 71))
        let guard := seeded.heap.size
        let before := { seeded with heap := seeded.heap.push ⟨.list [], false⟩, iterators := [guard] }
        let native := Functions.denoteBody resolved.program available (resolvedComp.body target) before
        let lowered := Functions.denoteBody resolved.program available (resolvedComp.lower target) before
        let sameState := fun (state loweredState : State) =>
          state.heap == loweredState.heap && state.iterators == [guard] && loweredState.iterators == [guard] &&
            (loweredState.bindingValue scratch).toOption == some (.scalar (.int 71)) &&
            (state.bindingValue target).toOption == (loweredState.bindingValue target).toOption &&
            state.slots Functions.Comprehensions.resultSlot == none &&
            loweredState.slots Functions.Comprehensions.operandSlot == none &&
            match state.read (.bound (globalSlot "effects")) with
            | .ok (.list address) _ => state.heap[address]?.map Cell.contents ==
                some (.list [.scalar (.int 1), .scalar (.int 1)])
            | _ => false
        match native, lowered with
        | .error (.unpackArity 2 1) state, .error (.unpackArity 2 1) loweredState =>
          fails && sameState state loweredState &&
            (state.bindingValue target).toOption == some (.scalar (.int 99)) &&
            state.heap[before.heap.size + 4]?.map Cell.contents == some (.binding (some (.scalar (.int 5)))) &&
            state.heap[before.heap.size + 5]?.map Cell.contents == some (.binding (some (.scalar (.int 2)))) &&
            state.heap[before.heap.size + 6]?.map Cell.contents == some (.binding (some (.scalar (.int 3))))
        | .ok .next state, .ok .next loweredState =>
          !fails && sameState state loweredState &&
            match state.bindingValue target with
            | .ok (.list address) => state.heap[address]?.map Cell.contents == some (.list [.scalar (.int 1)])
            | _ => false
        | _, _ => false
      | _ => false
    | _ => false
  | _ => false

#guard withRows starlark%[[[[1, [2, 3]]]]] false
#guard withRows starlark%[[[[1, [2, 3]], [5, [6]]]]] true

-- On success the ordinary module publication path freezes the result.
#guard
  let comp : ListComp := ⟨starlark%[(x, [y])], starlark%[[(1, [2])]], .yield starlark%[y]⟩
  match runModule [.assignListComp "out" comp] noImports {} with
  | .ok (.ok published state) =>
    match published.exports.lookup "out" with
    | some (.list address) =>
      (state.heap[address]?.map Cell.frozen).getD false && (published.exports.map Prod.fst == ["out"])
    | _ => false
  | _ => false

-- Later iterations of one evaluation keep prior writes to the new block.
#guard
  let comp : ListComp := ⟨starlark%[x], starlark%[[1, 0]],
    .filter starlark%[x or y] (.forIn starlark%[y] starlark%[[2]] (.yield starlark%[y]))⟩
  match runModule [.assignListComp "out" comp] noImports {} with
  | .ok (.ok published state) =>
    match published.exports.lookup "out" with
    | some (.list address) =>
      state.heap[address]?.map Cell.contents == some (.list [.scalar (.int 2), .scalar (.int 2)])
    | _ => false
  | _ => false

-- Each evaluation starts with fresh comprehension slots. On the second
-- visit to the same site, short circuiting no longer skips the unbound y.
#guard
  let comp : ListComp := ⟨starlark%[x], starlark%[source],
    .filter starlark%[x or y] (.forIn starlark%[y] starlark%[[2]] (.yield starlark%[y]))⟩
  let commands : List Command :=
    [.define "run" {} (.forIn "source" starlark%[[[1], [0]]] (.assignListComp "result" comp)),
     .eval starlark%[run()]]
  match runModule commands noImports {} with
  | .ok (.error (.runtime (.uninitialized binding)) state) =>
    binding == fileSlot "y" && state.iterators.isEmpty
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve

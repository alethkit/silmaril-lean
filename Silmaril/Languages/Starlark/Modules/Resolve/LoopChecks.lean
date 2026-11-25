module

import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve

open scoped Functions.Lowering.Quote

private def noImports : Catalog := fun _ => none

private def lists : Command := .define "items" { varargs := some "values" }
  (.ret (some starlark%[list(values)]))

private def callBody (body : Statement) : List Command :=
  [lists, .define "run" {} body, .assign "out" starlark%[run()]]

-- A loop target shadows the global throughout the function, including the operand.
-- Neither a pre-loop read nor an empty iteration initializes the target.
#guard
  let unbound := fun body =>
    match runModule (.assign "x" starlark%[list()] :: callBody body) noImports {} with
    | .ok (.error (.runtime (.uninitialized binding)) _) => binding == fileSlot "x"
    | _ => false
  unbound (.seq (.eval starlark%[x]) (.forIn "x" starlark%[items(7)] .pass)) &&
    unbound (.forIn "x" starlark%[x] .pass) &&
    unbound (.seq (.forIn "x" starlark%[items()] .pass) (.ret (some starlark%[x])))

-- Iteration writes the parameter's existing slot and an empty loop leaves it intact.
#guard
  let last : Command := .define "last" { positional := [⟨"x", none⟩], varargs := some "values" }
    (.seq (.forIn "x" starlark%[values] .pass) (.ret (some starlark%[x])))
  let commands := [last, .assign "nonempty" starlark%[last(99, 1, 2)], .assign "empty" starlark%[last(99)]]
  match runModule commands noImports {} with
  | .ok (.ok published _) =>
    decide (published.exports.lookup "nonempty" = some (.scalar (.int 2))) &&
      decide (published.exports.lookup "empty" = some (.scalar (.int 99)))
  | _ => false

-- A closure defined earlier captures the slot allocated for the later target.
#guard
  let body : Statement := .seq (.define "read" {} (.ret (some starlark%[x])))
    (.seq (.forIn "x" starlark%[items(3, 4)] .pass) (.ret (some starlark%[read()])))
  match runModule (callBody body) noImports {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.int 4)))
  | _ => false

-- `continue` skips the rest of the iteration. The inner `break` leaves the outer loop active.
#guard
  let inner : Statement := .forIn "y" starlark%[items(False, True)]
    (.seq (.branch starlark%[y] .breakLoop .continueLoop) (.eval starlark%[len(9)]))
  let body : Statement := .seq (.forIn "x" starlark%[items(10, 20)] inner)
    (.ret (some starlark%[x if y else len(9)]))
  match runModule (callBody body) noImports {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.int 20)))
  | _ => false

#guard
  let loop : Statement := .forIn "x" starlark%[items(7, 8)] (.ret (some starlark%[x]))
  match runModule (callBody (.seq loop (.eval starlark%[len(9)]))) noImports {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.int 7)))
  | _ => false

-- A quoted, reversed slice supplies a normalized source loop and initializes
-- the target even for reads after the loop.
#guard
  let loop : Statement := .forIn "x" starlark%[range(10, 3, -2)[::-2]] .pass
  match runModule (callBody (.seq loop (.ret (some starlark%[x])))) noImports {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.int 8)))
  | _ => false

-- Check iterator cleanup at the command boundary, before module restoration.
#guard
  let commands := callBody (.forIn "x" starlark%[items(7)] (.eval starlark%[len(x)]))
  match resolve commands with
  | .ok resolved =>
    let entered := enter resolved.source {}
    match runCommands resolved.program noImports resolved.source.commands entered with
    | .error (.runtime (.builtinType .len (.scalar (.int 7)))) state =>
      state.iterators.isEmpty &&
      match state.bindingValue (globalSlot "out") with
      | .error (.uninitialized binding) => binding == globalSlot "out"
      | _ => false
    | _ => false
  | _ => false

-- Skipped branches are checked. A nested definition starts its own loop-control scope.
#guard
  let rejected := fun body error => match runModule (callBody body) noImports {} with
    | .error (.validation (.syntax actual)) => actual == error
    | _ => false
  rejected (.branch starlark%[False] .breakLoop .pass) .breakOutsideLoop &&
    rejected (.forIn "x" starlark%[items()]
      (.define "nested" {} .continueLoop)) .continueOutsideLoop

-- Both pattern spellings collect names in the enclosing function. A closure
-- captures the later slot, and repeated names receive writes in source order.
#guard
  let body : Statement := .seq (.define "read" {} (.ret (some starlark%[y])))
    (.seq (.forInTarget starlark%[(x, y)] starlark%[[[1, 2], (3, 4), range(5, 7)]] .continueLoop)
      (.seq (.forInTarget starlark%[[x, x]] starlark%[[(7, 8)]] .breakLoop)
        (.ret (some starlark%[{(8, 6): True}[(x, read())]]))))
  match runModule (callBody body) noImports {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.bool true)))
  | _ => false

-- Even a later write in the flat pattern shadows the global in the operand.
#guard
  let body : Statement := .forInTarget starlark%[(x, y)] starlark%[y] .pass
  match runModule (.assign "y" starlark%[[]] :: callBody body) noImports {} with
  | .ok (.error (.runtime (.uninitialized name)) _) => name == fileSlot "y"
  | _ => false

#guard
  let body : Statement := .seq (.forInTarget starlark%[[]] starlark%[[(), [], range(0)]] .pass)
    (.forInTarget starlark%[[k, v]] starlark%[[{"z": 1, "a": 2}]]
      (.ret (some starlark%[{("z", "a"): True}[(k, v)]])))
  match runModule (callBody body) noImports {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.bool true)))
  | _ => false

-- Reject target forms outside the name-leaf profile statically,
-- including when the loop is unreachable or its iterable is empty.
#guard
  let reject := fun target => match runModule (callBody
    (.branch starlark%[False] (.forInTarget target starlark%[[]] .pass) .pass)) noImports {} with
    | .error .unsupportedLoopTarget => true
    | _ => false
  reject starlark%[(x, [y, 1])] && reject starlark%[[(x, xs[0]), y]] &&
    reject starlark%[(x, [len(y)])]

#guard
  let loop := Statement.forInTarget starlark%[[x, (x, [x, y])]]
    starlark%[[[1, (2, range(3, 5))]]] (.ret (some starlark%[{(3, 4): True}[(x, y)]]))
  match runModule (callBody loop) noImports {} with
  | .ok (.ok published _) => decide (published.exports.lookup "out" = some (.scalar (.bool true)))
  | _ => false

#guard
  let loop := Statement.forInTarget starlark%[(x, [y, z])] starlark%[z] .pass
  match runModule (.assign "z" starlark%[[]] :: callBody loop) noImports {} with
  | .ok (.error (.runtime (.uninitialized name)) _) => name == fileSlot "z"
  | _ => false

-- The failed call leaves a closure that can read its escaped target slots.
-- The second row wrote a before the nested mismatch, and skipped its body.
#guard
  let loop := Statement.forInTarget starlark%[(a, [b, c], d)] starlark%[rows]
    (.setIndex starlark%[seen] starlark%[0] starlark%[a])
  let body := Statement.seq (.define "read" {} (.ret (some starlark%[(a, b, c, d)])))
    (.seq (.setIndex starlark%[saved] starlark%[0] starlark%[read]) loop)
  let commands : List Command := [.assign "rows" starlark%[[[1, [2, 3], 4], [5, [6], 7]]],
    .assign "seen" starlark%[[0]], .assign "saved" starlark%[[None]],
    .define "run" {} body, .eval starlark%[run()]]
  match resolve commands with
  | .ok resolved =>
    match runCommands resolved.program noImports resolved.source.commands (enter resolved.source {}) with
    | .error (.runtime (.unpackArity 2 1)) state =>
      match Functions.Lowering.Resolve.resolveTracked { globals := globalNames commands }
        starlark%[{(5, 2, 3, 4): seen[0]}[saved[0]()]] with
      | .ok (observe, _) =>
        match Functions.Lowering.denoteExpr resolved.program (List.range resolved.program.size) observe state with
        | .ok (.scalar (.int 1)) final => state.iterators.isEmpty && final.iterators.isEmpty
        | _ => false
      | _ => false
    | _ => false
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve

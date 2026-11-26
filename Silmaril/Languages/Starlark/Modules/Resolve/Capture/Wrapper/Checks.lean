module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper

open scoped Functions.Lowering.Quote
open Lists (State Cell)

private def leaf : Forwarding.Chain :=
  .mixed "leaf" ["i"] ⟨"first", starlark%[box], starlark%[i], .plain starlark%[rows[i]], starlark%[box[i]]⟩

private def chain : Forwarding.Chain := .wrapper "outer" ["box"] (.wrapper "bridge" ["tag"] leaf)

private def root : Command := .define chain.name (.required chain.parameters) chain.body

private def first : List Command := [root, .assign "box" starlark%[[3]], .assign "bridge_saved" starlark%[outer(box)]]

private def escaped : Command := .assign "saved" starlark%[bridge_saved(0)]

private def rows : Command := .assign "rows" starlark%[[(0, 9)]]

private def observation : Command := .assign "out" starlark%[saved(0)]

private def commands : List Command := first ++ [escaped, rows, observation]

private def functionCount (state : State) : Nat :=
  (state.heap.toList.filter fun cell => match cell.contents with
    | .function _ => true
    | _ => false).length

-- Both wrapper calls finish before invoking the mixed leaf. The leaf
-- modifies the original list and uses the later-initialized global.
#guard
  match runModule commands (fun _ => none) {} with
  | .ok (.ok published final) =>
    match published.exports.lookup "box", published.exports.lookup "saved" with
    | some (.list box), some (.function saved) =>
      match final.heap[box]?.map Cell.contents, final.heap[saved]?.map Cell.contents with
      | some (.list [.scalar (.int 9)]), some (.function closure) =>
        functionCount final == 3 && closure.declaration == 0 &&
          final.heap[box]?.map Cell.frozen == some true && final.heap[saved]?.map Cell.frozen == some true &&
          published.exports.lookup "out" == some (.scalar (.int 9))
      | _, _ => false
    | _, _ => false
  | _ => false

-- Arity rejection in the second wrapper retains the first two closures.
#guard
  match runModule (first ++ [.assign "saved" starlark%[bridge_saved()], rows, observation]) (fun _ => none) {} with
  | .ok (.error (.runtime (.missingArguments ["tag"])) final) => functionCount final == 2
  | _ => false

-- The leaf exists before rows has a value. The reached failure retains
-- the closures and leaves the original list unchanged.
#guard
  match runModule (first ++ [escaped, observation, rows]) (fun _ => none) {} with
  | .ok (.error (.runtime (.uninitialized slot)) final) =>
    slot == globalSlot "rows" && functionCount final == 3 &&
      final.heap.toList.any (fun cell => cell.contents == .list [.scalar (.int 3)] && !cell.frozen)
  | _ => false

-- The reached root and list setup leave a callable value. Evaluate just
-- the two value-level wrapper returns using the compositional denotation.
#guard
  match resolve commands with
  | .ok resolved =>
    match runCommands resolved.program (fun _ => none) (resolved.source.commands.take 2) (enter resolved.source {}) with
    | .ok () state =>
      match state.bindingValue (globalSlot "outer"), state.bindingValue (globalSlot "box") with
      | .ok outer, .ok box =>
        match denoteWalk resolved.program [[box], [.scalar (.int 0)]] outer state with
        | .ok (.function address) final =>
          match final.heap[address]?.map Cell.contents with
          | some (.function closure) => closure.declaration == 0 && functionCount final == 3
          | _ => false
        | _ => false
      | _, _ => false
    | _ => false
  | .error _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper

module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry

open scoped Functions.Lowering.Quote
open Lists (Cell)
open Block (ModuleBinders)

private def root : Command :=
  .define "read_row" (.required ["index"]) (.ret (some starlark%[rows[index]]))

private def rows : Command := .assign "rows" starlark%[[7, 9]]

private def early : List Command := [root, .eval starlark%[read_row(1)], rows]

example : ModuleBinders early ["read_row", "rows"] :=
  .cons (.define ..) (.cons (.eval _) (.cons (.assign ..) .nil))

private def firstRead : List Command := [.eval starlark%[rows], rows]

example {resolved : ResolvedModule} (checked : resolve firstRead = .ok resolved) :
    runModule firstRead (fun _ => none) {} =
      .ok (.error (.runtime (.uninitialized (globalSlot "rows")))
        (restoreThread {} (enter resolved.source {}))) :=
  checked_first_read_error (.cons (.eval _) (.cons (.assign ..) .nil)) checked
    (by decide) (by simp) _ _

example : Binds ["x", "y"] [.scalar (.int 3), .scalar (.int 5)]
    (.ok [(fileSlot "x", .scalar (.int 3)), (fileSlot "y", .scalar (.int 5))]) :=
  .success (.cons (.cons .nil))

example : Binds ["x", "y"] [.scalar (.int 3)] (.error (.missingArguments ["y"])) :=
  .missing (by decide)

example : Binds [] [.scalar (.int 3)] (.error (.arity 0 1)) :=
  .surplus (by decide)

-- A reused heap does not supply a value for a new global slot. The
-- root definition succeeds, then the call reaches the uninitialized read.
#guard
  let caller : Lists.State := { heap := #[⟨.binding (some (.scalar (.int 100))), false⟩] }
  match runModule early (fun _ => none) caller with
  | .ok (.error (.runtime (.uninitialized binding)) state) =>
    binding == globalSlot "rows" &&
      state.heap[0]?.map Cell.contents == some (.binding (some (.scalar (.int 100))))
  | _ => false

#guard
  match runModule [root, rows, .assign "out" starlark%[read_row(1)]] (fun _ => none) {} with
  | .ok (.ok published _) => published.exports.lookup "out" == some (.scalar (.int 9))
  | _ => false

#guard
  match runModule [root, .eval starlark%[read_row()], rows] (fun _ => none) {} with
  | .ok (.error (.runtime (.missingArguments ["index"])) _) => true
  | _ => false

#guard
  match runModule [root, .eval starlark%[read_row(0, 1)], rows] (fun _ => none) {} with
  | .ok (.error (.runtime (.arity 1 2)) _) => true
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry

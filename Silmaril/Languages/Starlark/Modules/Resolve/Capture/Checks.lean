module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture

open scoped Functions.Lowering.Quote
open Lists

private def child : MixedBody :=
  ⟨"i", starlark%[alias], starlark%[i],
    .list ⟨starlark%[item], starlark%[rows[i]], .yield starlark%[item]⟩,
    starlark%[alias[late]]⟩

private def slots : List Binding := [globalSlot "rows", fileSlot "alias", fileSlot "late"]

-- The child parameter shadows a parent local. The alias resolves to the
-- parent rather than its module namesake. Repeated reads keep their first
-- positions and unused names contribute no address.
example : Selects ⟨["i"], ["alias", "i", "late", "unused"], ["alias", "rows"]⟩
    [globalSlot "rows", fileSlot "i", fileSlot "alias", fileSlot "i", fileSlot "alias", fileSlot "late"]
    (slots.map fun binding => ⟨binding, binding⟩) :=
  .module (.module (by decide) (by decide) (by decide))
    (.owned (.owned (by decide)) (.enclosing (.enclosing (by decide) (by decide))
      (.enclosing (.enclosing (by decide) (by decide)) .nil)))

private def make (earlyCall : Bool) : Command :=
  let tail := Statement.seq (.assign "late" starlark%[1]) (.ret (some starlark%[inner]))
  .define "make" (.required ["alias", "unused"])
    (.seq (.assign "i" starlark%[1])
      (.seq (.define "inner" (.required ["i"]) child.statement)
        (.seq (.assign "alias" starlark%[replacement])
          (if earlyCall then .seq (.eval starlark%[inner(0)]) tail else tail))))

private def setup : List Command :=
  [.assign "alias" starlark%[[100]], .assign "original" starlark%[[3, 30]],
   .assign "replacement" starlark%[[4, 40]]]

private def rows : Command := .assign "rows" starlark%[[[0, 9], [0, 6]]]

private def escaped : Command := .assign "escaped" starlark%[make(original, 123)]

private def success : List Command :=
  setup ++ [make false, escaped, rows,
    .assign "out" starlark%[(escaped(0), original[0], replacement[0], alias[0])]]

-- The emitted list follows evaluation order, with globals represented as
-- slots. Both the source and target of every capture use the selected name.
#guard
  match resolve success with
  | .ok result =>
    match result.program[0]? with
    | some declaration =>
      declaration.locals.isEmpty &&
        declaration.free.map Functions.FreeName.source == slots &&
        declaration.free.map Functions.FreeName.target == slots
    | none => false
  | .error _ => false

-- The read of late follows its initialization in the parent. The shared
-- alias slot sees the rebound list, and the write mutates that list alone.
#guard
  match runModule success (fun _ => none) {} with
  | .ok (.ok published state) =>
    match published.exports.lookup "out" with
    | some (.tuple address) =>
      match state.heap[address]?.map Cell.contents with
      | some (.tuple values _) =>
        values == [.scalar (.int 40), .scalar (.int 3), .scalar (.int 9), .scalar (.int 100)]
      | _ => false
    | _ => false
  | _ => false

-- Capturing a slot succeeds before initialization. Reading it early
-- fails in the child after any earlier assignment effects.
#guard
  match runModule (setup ++ [rows, make true, escaped]) (fun _ => none) {} with
  | .ok (.error (.runtime (.uninitialized slot)) state) =>
    slot == fileSlot "late" &&
      state.heap.any (fun cell => cell.contents == .list [.scalar (.int 9), .scalar (.int 40)])
  | _ => false

#guard
  match runModule (setup ++ [make false, escaped, .eval starlark%[escaped(0)], rows]) (fun _ => none) {} with
  | .ok (.error (.runtime (.uninitialized slot)) _) => slot == globalSlot "rows"
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture

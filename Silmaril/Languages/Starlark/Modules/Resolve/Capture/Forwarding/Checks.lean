module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding

open scoped Functions.Lowering.Quote
open Lists

private def body : MixedBody :=
  ⟨"i", starlark%[box], starlark%[i],
    .list ⟨starlark%[item], starlark%[rows[i]], .yield starlark%[item]⟩,
    starlark%[box[i]]⟩

private def child : Chain := .wrapper "transit" [] (.wrapper "relay" [] (.mixed "leaf" ["i"] body))

-- The two forwarding blocks and the leaf own no box. The lookup
-- selects the nearer of two owning functions with the same parameter.
example : Nearest "box" [["i"], ["leaf"], ["relay"], ["box", "transit"], ["box", "nearest"]] 3 :=
  .farther (by decide) (.farther (by decide) (.farther (by decide) (.owns (by decide))))

private def outer : Command :=
  let nearest := Statement.seq child.definition
    (.seq (.assign "escapedLeaf" starlark%[transit()()])
      (.seq (.assign "box" starlark%[replacement]) (.ret (some starlark%[escapedLeaf]))))
  .define "outer" (.required ["box"])
    (.seq (.define "nearest" (.required ["box"]) nearest) (.ret (some starlark%[nearest(box)])))

private def setup : List Command :=
  [.assign "box" starlark%[[100]], .assign "original" starlark%[[3]], .assign "replacement" starlark%[[4]],
   outer, .assign "escaped" starlark%[outer(original)]]

private def rows : Command := .assign "rows" starlark%[[[0, 9], [0, 6]]]
private def commands : List Command :=
  setup ++ [rows, .assign "out" starlark%[(escaped(0), original[0], replacement[0], box[0])]]

private def sources (declaration : Functions.Declaration) : List Binding :=
  declaration.free.map Functions.FreeName.source

-- The two wrappers have no direct read of box or rows. Both propagate
-- the leaf's demands, and forwarding stops at the nearer box owner.
#guard
  match resolve commands with
  | .ok resolved =>
    resolved.program.toList.map sources ==
      List.replicate 3 [globalSlot "rows", fileSlot "box"] ++
        List.replicate 2 [globalSlot "rows", globalSlot "replacement"]
  | .error _ => false

-- The leaf exists before the nearer parent rebinds its box. After all
-- enclosing calls have returned it mutates the replacement list.
#guard
  match runModule commands (fun _ => none) {} with
  | .ok (.ok published state) =>
    match published.exports.lookup "out", published.exports.lookup "escaped" with
    | some (.tuple out), some (.function escaped) =>
      match state.heap[out]?.map Cell.contents, state.heap[escaped]?.map Cell.contents with
      | some (.tuple values _), some (.function closure) =>
        values == [.scalar (.int 9), .scalar (.int 3), .scalar (.int 9), .scalar (.int 100)] &&
          closure.captures.map (fun capture => (capture.binding, capture.localCell)) ==
            [(globalSlot "rows", false), (fileSlot "box", true)]
      | _, _ => false
    | _, _ => false
  | _ => false

-- The uninitialized module slot can be forwarded before it gets a value.
#guard
  match runModule (setup ++ [.eval starlark%[escaped(0)], rows]) (fun _ => none) {} with
  | .ok (.error (.runtime (.uninitialized slot)) _) => slot == globalSlot "rows"
  | _ => false

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding

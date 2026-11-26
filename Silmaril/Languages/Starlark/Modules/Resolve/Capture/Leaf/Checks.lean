module

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Defs
meta import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Defs

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf

open scoped Functions.Lowering.Quote
open Lists (State Cell)
open Lists.Iteration (Cursor UnpacksValue)

private def leaf : Forwarding.Chain :=
  .mixed "leaf" ["idx"] ⟨"idx", starlark%[box], starlark%[idx], .plain starlark%[pair], starlark%[later]⟩

private def chain : Forwarding.Chain := .wrapper "outer" ["box"] (.wrapper "bridge" [] leaf)

private def setup : List Command :=
  [.define chain.name (.required chain.parameters) chain.body,
    .assign "box" starlark%[[3]], .assign "pair" starlark%[(0, 9)],
    .assign "bridge_saved" starlark%[outer(box)], .assign "saved" starlark%[bridge_saved()]]

private def readLater : Command := .assign "later" starlark%[9]
private def invoke : Command := .assign "out" starlark%[saved(1)]

-- The first leaf replaces the parameter before the second leaf reaches its
-- index read. Both wrapper calls already returned, so the list is shared
-- through the escaped capture. Check every export and the frozen list.
#guard
  match runModule (setup ++ [readLater, invoke]) (fun _ => none) {} with
  | .ok (.ok published state) =>
    match published.exports.lookup "outer", published.exports.lookup "box", published.exports.lookup "pair",
        published.exports.lookup "bridge_saved", published.exports.lookup "saved" with
    | some (.function outer), some (.list box), some (.tuple pair), some (.function bridge), some (.function saved) =>
      published.exports ==
        [("outer", .function outer), ("box", .list box), ("pair", .tuple pair),
          ("bridge_saved", .function bridge), ("saved", .function saved),
          ("later", .scalar (.int 9)), ("out", .scalar (.int 9))] &&
        state.heap[box]?.map Cell.contents == some (.list [.scalar (.int 9)]) &&
        [outer, box, pair, bridge, saved].all (fun address => state.heap[address]?.map Cell.frozen == some true)
    | _, _, _, _, _ => false
  | _ => false

private def isUnset (initial final : State) (name : String) : Bool :=
  match initial.slots (globalSlot name) with
  | some (.owned address) => final.heap[address]?.map Cell.contents == some (.binding none)
  | _ => false

-- The leaf stores through its capture before the uninitialized return
-- read. This leaves the destination and the skipped suffix uninitialized.
#guard
  let commands := setup ++ [invoke, readLater]
  match resolve commands, runModule commands (fun _ => none) {} with
  | .ok resolved, .ok (.error (.runtime (.uninitialized slot)) state) =>
    slot == globalSlot "later" &&
      isUnset (enter resolved.source {}) state "out" && isUnset (enter resolved.source {}) state "later" &&
      state.heap.toList.any (fun cell => cell.contents == .list [.scalar (.int 9)] && !cell.frozen)
  | _, _ => false

private def plan : Plan :=
  ⟨fileSlot "idx", globalSlot "pair", fileSlot "box", fileSlot "idx", globalSlot "later"⟩

private def leafFrame : State := {
  heap := #[⟨.list [.scalar (.int 3)], false⟩,
    ⟨.tuple [.scalar (.int 0), .scalar (.int 9)] none, false⟩]
  bindings := fun slot =>
    if slot == plan.index then some (.scalar (.int 1))
    else if slot == plan.receiver then some (.list 0)
    else if slot == plan.rhs then some (.tuple 1)
    else none
}

-- Construct the independent assignment derivation, then check the late
-- return error and retained store through both resolved semantics.
example :
    let named := leafFrame.write plan.destination (.scalar (.int 0))
    let final := { named with heap := leafFrame.heap.setIfInBounds 0 ⟨.list [.scalar (.int 9)], false⟩ }
    let result : Lists.Outcome Lists.Iteration.Flow := .error (.uninitialized plan.returned) final
    Functions.Exec #[] [] leafFrame plan.code result ∧
      Functions.denoteBody #[] [] plan.code leafFrame = result := by
  have unpacked : UnpacksValue leafFrame (.tuple 1) 2 (.ok [.scalar (.int 0), .scalar (.int 9)] leafFrame) :=
    .items (cursor := Cursor.items [.scalar (.int 0), .scalar (.int 9)]) (guard := some 1)
      rfl rfl (.next rfl (.next rfl (.done rfl)))
  have legal : plan.Legal := by
    intro binding member
    simp [plan] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  have independent := Runs.leaves (plan := plan) (state := leafFrame) rfl unpacked
  have clean : noPrivateSlots leafFrame := by
    unfold noPrivateSlots
    intro _ _
    rfl
  exact leaf_sound #[] [] plan leafFrame legal clean independent

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Leaf

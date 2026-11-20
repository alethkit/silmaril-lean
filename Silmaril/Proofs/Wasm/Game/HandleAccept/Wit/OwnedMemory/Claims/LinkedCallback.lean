module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}
  {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}

private theorem silent (count : Nat) :
    PayloadPrefix.visible (List.replicate count .tau : List (Label (core3 grow) (HostState sig))) = [] := by
  induction count with
  | zero => rfl
  | succ _ ih => simpa only [List.replicate_succ, PayloadPrefix.visible, List.filter_cons, Bool.false_eq_true, ↓reduceIte] using ih

theorem replay {left right last : State grow sig} {visibleLabels}
    (path : Prefix profile ready bindings first left visibleLabels last)
    (paired : HostFrame.Paired first second left right) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    ∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels last ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second last other ∧
      PayloadPrefix.visible leftLabels = visibleLabels ∧ PayloadPrefix.visible rightLabels = visibleLabels := by
  induction path generalizing right with
  | done cfg => exact ⟨[], [], right, .refl _, .refl _, paired, rfl, rfl⟩
  | step inside growth run _ ih =>
    obtain ⟨_, replay, matched⟩ := HostFrame.interior_step paired inside growth run
    obtain ⟨leftLabels, rightLabels, other, lhs, rhs, still, seenLeft, seenRight⟩ := ih matched
    refine ⟨_ :: leftLabels, _ :: rightLabels, other, .cons growth run lhs,
      replay.append rhs, still, ?_, ?_⟩
    · exact (List.filter_append [_] leftLabels).trans (congrArg (PayloadPrefix.visible [_] ++ ·) seenLeft)
    · exact (List.filter_append [_] rightLabels).trans (congrArg (PayloadPrefix.visible [_] ++ ·) seenRight)
  | closedGive callout _ ih =>
    obtain ⟨leftCount, rightCount, _, _, _, lhs, rhs, _, matched, _, _⟩ :=
      Plain.parked_closed_give_rejoin bindings callout.name callout.type callout.args callout.inst
        callout.destination callout.schema paired callout.thread profile ready callout.parked
        callout.calling callout.linked callout.caller callout.live callout.closed
    obtain ⟨leftLabels, rightLabels, other, leftTail, rightTail, still, seenLeft, seenRight⟩ := ih matched
    refine ⟨_, _, other, lhs.append leftTail, rhs.append rightTail, still, ?_, ?_⟩
    · rw [PayloadPrefix.visible, List.filter_append]
      exact (congrArg (· ++ PayloadPrefix.visible leftLabels) (silent leftCount)).trans seenLeft
    · rw [PayloadPrefix.visible, List.filter_append]
      exact (congrArg (· ++ PayloadPrefix.visible rightLabels) (silent rightCount)).trans seenRight

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback

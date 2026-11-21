module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.FlatStrings.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicFlatStrings

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.FlatStrings

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {schema : TypeOf}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

private theorem refineShape (destination : RecordDestination) (depth : Nat) (field : Field)
    (shape : Shape depth field)
    (reached : ∀ leaf, Field.Descendant field leaf → (∃ item : StringField, item.field = leaf) → StringField.Fits destination leaf) :
    FlatNestedFits (StringField.Fits destination) depth field := by
  induction depth generalizing field with
  | zero => exact reached field (.self field) shape
  | succ depth ih =>
    cases childrenAt : flatChildren field with
    | none =>
      simp only [FlatStrings.Shape, FlatNestedFits, childrenAt] at shape
      simpa only [FlatNestedFits, childrenAt] using reached field (.self field) shape
    | some children =>
      simp only [FlatStrings.Shape, FlatNestedFits, childrenAt] at shape
      simp only [FlatNestedFits, childrenAt]
      intro child member
      apply ih child (shape child member)
      intro leaf path leafShape
      apply reached leaf _ leafShape
      cases field <;> cases childrenAt
      · exact .aggregate member path
      · exact .fixed member path

private theorem initialFrame (call : PayloadRoot.Site grow sig (.flat schema)) (next : call.ReferenceNext)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) :
    ChildFrameOver older call.checked (call.reference next) call.cursor call.cursor := by
  have segments : ∀ frames, List.Forall₂ (ReturnFrame.Related.Segment older) frames frames :=
    fun _ => List.forall₂_same.mpr fun frame _ => .same frame
  have active : ∀ act, ReturnFrame.Related.Active older act act := fun ⟨_, _, frames⟩ => .mk (segments frames)
  have saved : ∀ act, ReturnFrame.Related.Saved older act act
    | none => .none
    | some act => .some (active act)
  exact ⟨rfl, rfl, rfl, rfl, List.forall₂_same.mpr fun act _ => saved act, rfl,
    segments call.cursor.frames, List.forall₂_same.mpr fun act _ => active act⟩

theorem parked (call : PayloadRoot.Site grow sig (.flat schema)) (linked : call.Linked bindings)
    (depth : Nat) (next : call.ReferenceNext) (shape : Shape depth call.field)
    {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (Body call depth next profile ready bindings) := by
  apply call.parked_after_fit linked
  intro admitted
  obtain ⟨plan, compiled⟩ := linked.compiled
  have fits : FlatNestedFits (StringField.Fits call.destination) depth call.field := by
    apply refineShape call.destination depth call.field shape
    intro leaf path leafShape
    obtain ⟨item, equal⟩ := leafShape
    rw [← equal] at path
    have checked := (call.destination.compiled_payload_descendant call.inst (sig.payload call.tag)
      call.payload .flat (plan := plan) compiled admitted path).2
    exact ⟨item, equal, by simpa only [StringField.field, Field.type, Field.value, Lower.fits, decide_eq_true_eq] using checked⟩
  unfold Body
  exact nested_flat_strings call.destination call.inst depth call.field
    (call.destination.check_width call.start.store linked.destination) realloc fits
    0 call.reply next call.checked (call.reference next) call.cursor call.cursor (initialFrame call next _)
    (Core3.Grows.refl _) rfl (call.reference_at linked next)
    _ (fun _ _ _ _ _ frame _ checked canonical => ⟨frame, checked, canonical⟩)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicFlatStrings

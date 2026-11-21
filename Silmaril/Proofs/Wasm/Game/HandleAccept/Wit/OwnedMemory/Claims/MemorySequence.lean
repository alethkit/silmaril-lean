module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Defs
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Width.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

theorem slotsMap (mode : Track) (width : AddrType) {premise target : Field → Nat → Prop}
    (convert : ∀ item address, premise item address → target item address) (items : List Field) (cursor : Nat)
    (slots : mode.Slots width premise items cursor) : mode.Slots width target items cursor := by
  induction items generalizing cursor with
  | nil => exact trivial
  | cons item rest ih => exact ⟨convert item _ slots.1, ih _ slots.2⟩

private theorem focusStep (mode : Track) (destination : RecordDestination) (inst : InstId) (item : Field) (rest : List Field)
    (cursor : Nat) (canonNext : CanonNext grow sig) (right : State grow sig) (canon : Cursor (E := core3 grow) (HostState sig))
    (width : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (atProgram : right.ctl = canon.control (mode.canonical destination inst (item :: rest) cursor >>= canonNext)) :
    Steps profile ready (specDispatch ready (host bindings)) right mode.readLabels
      (focus mode destination inst item cursor right canon
        (canonTail mode destination inst rest (mode.slot destination.width item cursor).2 canonNext)) := by
  cases mode with
  | elements stride =>
    let entered := focus (.elements stride) destination inst item cursor right canon
      (canonTail (.elements stride) destination inst rest (cursor + stride) canonNext)
    have control : right.ctl = entered.ctl := by
      let head : Session grow sig Unit := CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
        destination.width item (.memory cursor)
      let tail : Session grow sig Unit := CanonicalTree.elements Limits.spec Quirks.none (destination.context inst)
        destination.width rest .value stride (cursor + stride)
      rw [atProgram]
      change canon.control ((head.bind (fun () => tail)).bind canonNext) =
        canon.control (head.bind (fun () => tail.bind canonNext))
      rw [Prog.bind_assoc]
    have same : entered = right :=
      (congrArg (fun ctl => { right with ctl }) control.symm).trans (by cases right; rfl)
    change Steps profile ready (specDispatch ready (host bindings)) right [] entered
    rw [same]
    exact .refl right
  | fields =>
    let cx := destination.context (grow := grow) inst
    let body := fun current =>
      let area := layout current item.type
      let address := alignTo cursor area.alignment
      CanonicalTree.field Limits.spec Quirks.none cx destination.width item (.memory address) >>= fun () =>
        CanonicalTree.memory Limits.spec Quirks.none cx destination.width rest (address + area.size) >>= canonNext
    have atRead : right.ctl = canon.control (ptrType cx >>= body) := by
      rw [atProgram]
      congr 1
      simp only [Track.canonical, CanonicalTree.memory, Prog.bind_eq, Prog.bind_assoc, body, cx]
      congr 1
      funext current
      let area := layout current item.type
      let address := alignTo cursor area.alignment
      let head : Session grow sig Unit := CanonicalTree.field Limits.spec Quirks.none cx destination.width item (.memory address)
      let tail : Session grow sig Unit := CanonicalTree.memory Limits.spec Quirks.none cx destination.width rest (address + area.size)
      change (head.bind (fun () => tail)).bind canonNext = head.bind (fun () => tail.bind canonNext)
      rw [Prog.bind_assoc]
    have step := (CoreGrowthSteps.refl (profile := profile) (ready := ready) (dispatch := specDispatch ready (host bindings)) right).read_width
      cx rfl width body atRead
    exact step.steps

theorem replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (index cursor : Nat)
    (compare : FieldComparison grow sig) (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (slots : mode.Slots destination.width (FieldRule compare older origin destination inst) items cursor)
    (ends : ∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon)
    (checkAt : left.ctl = check.control (mode.checked destination inst items index cursor >>= checkNext))
    (canonAt : right.ctl = canon.control (mode.canonical destination inst items cursor >>= canonNext)) :
    Replay profile ready bindings mode destination inst compare checkNext canonNext finish items index cursor left right check canon := by
  induction items generalizing index cursor left right check canon with
  | nil =>
    change finish left right check canon
    apply ends left right check canon frame growth
    · cases mode <;> simpa only [Track.checked, Record.Effects.memory, Record.Effects.elements, Prog.bind_eq, Prog.pure_eq,
        Prog.pure_bind'] using checkAt
    · cases mode <;> simpa only [Track.canonical, CanonicalTree.memory, CanonicalTree.elements, Prog.bind_eq, Prog.pure_eq,
        Prog.pure_bind'] using canonAt
  | cons item rest ih =>
    rw [Replay]
    change FieldRule compare older origin destination inst item (mode.slot destination.width item cursor).1 ∧
      mode.Slots destination.width (FieldRule compare older origin destination inst) rest (mode.slot destination.width item cursor).2 at slots
    have width := frame.store ▸ growth.memAddrType present
    refine ⟨focusStep mode destination inst item rest cursor canonNext right canon width canonAt, ?_⟩
    let nextAddress := (mode.slot destination.width item cursor).2
    let nextCheck := checkTail mode destination inst rest (index + 1) nextAddress checkNext
    let nextCanon := canonTail mode destination inst rest nextAddress canonNext
    let focused := focus mode destination inst item cursor right canon nextCanon
    have paired : ChildFrameOver older left focused check canon :=
      ⟨frame.store, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
    refine slots.1 index nextCheck nextCanon left focused check canon paired growth ?_ rfl _ ?_
    · rw [checkAt]
      congr 1
      cases mode <;> simp only [Track.checked, Track.slot, Record.Effects.memory, Record.Effects.elements, Prog.bind_eq, Prog.bind_assoc]
      all_goals
        congr 1
        funext verdict
        cases verdict with
        | error issue => rfl
        | ok result => cases result; rfl
    · intro reached reference pushedCheck pushedCanon paired grown checked canonical
      exact ih (index + 1) (mode.slot destination.width item cursor).2 paired grown slots.2 checked canonical

theorem mixedRule {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (destination : RecordDestination) (inst : InstId) (item : Field) (address : Nat)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    {addr : Nat} (realloc : destination.realloc = some addr) (slot : MixedSlot destination bytes item address) :
    FieldRule (mixed profile ready bindings older destination inst) older origin destination inst item address := by
  intro index checkNext canonNext left right check canon frame growth checkAt canonAt finish ends
  rcases slot with handle | ⟨⟨str, rfl, fit⟩, aligned, bounds⟩
  · exact .inl ⟨handle, frame.handle_field_then destination inst item handle index (.memory address) checkNext canonNext
      growth checkAt canonAt (fun () => ends)⟩
  · obtain ⟨reachedBytes, sizeAt, widened⟩ := growth.memSize sized
    change (core3 grow).memSize? left.store.core destination.memory = some reachedBytes at sizeAt
    change address % (layout destination.width (.prim .string : TypeOf)).alignment.bytes = 0 at aligned
    change address + (layout destination.width (.prim .string : TypeOf)).size ≤ bytes at bounds
    have placed : rootPlacement destination left.store (.prim .string) (.memory address) = .ok () := by
      simp [rootPlacement, placement, aligned, sizeAt, Nat.not_lt.mpr (bounds.trans widened)]
      rfl
    exact .inr ⟨str, rfl, frame.string_field_then destination inst str (.memory address) index checkNext canonNext
      growth present realloc fit placed checkAt canonAt (fun () => ends)⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence

module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.NestedRecord.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Component.Reference.ABI.Layout.Thms
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.NestedRecord

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.NestedRecord

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

private theorem appendSteps {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {start middle finish : State grow sig} {first second : List (Label (core3 grow) (HostState sig))}
    (leading : Steps profile ready dispatch start first middle) (trailing : Steps profile ready dispatch middle second finish) :
    Steps profile ready dispatch start (first ++ second) finish := by
  induction leading with
  | refl => exact trailing
  | cons step _ next => exact .cons step (next trailing)

private theorem widthOf (site : Site) {origin store : CStore (core3 grow)} {bytes : Nat}
    (region : site.Region origin bytes) (growth : Core3.Grows origin.core store.core) :
    ptrTypeIn store (site.destination.context site.inst) = site.destination.width := by
  have reached : (core3 grow).memAddrType? store.core site.destination.memory = some site.destination.width :=
    growth.memAddrType region.width
  simp [ptrTypeIn, CanonOpts.ptrType, RecordDestination.context, reached]

private theorem suffix (site : Site) {origin : CStore (core3 grow)} {bytes : Nat} (region : site.Region origin bytes)
    (child : ∀ item ∈ site.following, MemoryChildRule profile ready (specDispatch ready (host (grow := grow) bindings))
      site.destination site.inst item item.type)
    (left right : State grow sig) (growth : Core3.Grows origin.core right.store.core) :
    CompareKeepingAt profile ready (specDispatch ready (host (grow := grow) bindings))
      (fun store => Core3.Grows origin.core store.core) left right site.checkedTail site.canonicalTail := by
  let layouts := site.fields.map fun item => layout site.destination.width item.type
  have layoutEq : layout site.destination.width site.schema = recordLayout layouts :=
    compiled_aggregate_layout site.destination.width region.layoutMatch
  have aligned := region.aligned
  have bounds := region.fits
  rw [layoutEq] at aligned bounds
  apply memory_fields_at site.destination site.inst site.following site.advance (site.index + 1)
    (fun _ grown => widthOf site region grown) _ left right growth
  intro slot item address found placed checked canonical grown
  have member : layouts[slot + 1]? = some (layout site.destination.width item.type) := by
    simp only [layouts, Site.fields, List.map_cons, List.getElem?_cons_succ, List.getElem?_map, found, Option.map_some]
  have offset : (fieldOffsets site.base layouts)[slot + 1]? = some address := by
    simpa only [layouts, Site.fields, List.map_cons, fieldOffsets, List.getElem?_cons_succ, placeField,
      Site.advance, Site.address, Site.headLayout] using placed
  obtain ⟨_, addressAligned, fits⟩ := recordLayout_field_fits layouts site.base (slot + 1) address _ aligned member offset
  exact child item (List.mem_of_getElem? found) origin (site.index + 1 + slot) address bytes
    region.width region.sized addressAligned (fits.trans bounds) checked canonical grown

theorem atCursor (site : Site) {origin : CStore (core3 grow)} {bytes : Nat} (region : site.Region origin bytes)
    (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig)
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (growth : Core3.Grows origin.core right.store.core)
    (children : ∀ item ∈ site.entries, MemoryChildRule profile ready (specDispatch ready (host (grow := grow) bindings))
      site.destination site.inst item site.element)
    (following : ∀ item ∈ site.following, MemoryChildRule profile ready (specDispatch ready (host (grow := grow) bindings))
      site.destination site.inst item item.type)
    (checkAt : left.ctl = cursor.control (Record.Effects.memory recordClaims Limits.spec Quirks.none
      (site.destination.context site.inst) site.destination.width site.fields site.base site.index >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.memory Limits.spec Quirks.none
      (site.destination.context site.inst) site.destination.width site.fields site.base >>= canonNext)) :
    site.Outcome profile ready bindings origin left right cursor checkNext canonNext := by
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  let cx := site.destination.context (grow := grow) site.inst
  let keep := fun (store : CStore (core3 grow)) => Core3.Grows origin.core store.core
  let checkHeadNext := checkedSequenceNext id (fun _ : Unit => site.checkedTail) checkNext
  let canonHeadNext := fun _ : Unit => site.canonicalTail >>= canonNext
  have checkHead : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx
      site.destination.width site.head site.index (.memory site.address) >>= checkHeadNext) := by
    rw [Site.fields, Record.Effects.memory] at checkAt
    simp only [Prog.bind_eq, Prog.bind_assoc] at checkAt ⊢
    convert checkAt using 4
    change Prog.bind (Record.Effects.field recordClaims Limits.spec Quirks.none cx site.destination.width
      site.head site.index (.memory site.address)) checkHeadNext = _
    apply congrArg (Prog.bind (Record.Effects.field recordClaims Limits.spec Quirks.none cx
      site.destination.width site.head site.index (.memory site.address)))
    funext verdict
    cases verdict with
    | ok value => cases value; rfl
    | error _ => rfl
  have later (_ : Unit) (entered reference : State grow sig) (grown : keep reference.store) :
      CompareKeepingAt profile ready dispatch keep entered reference site.checkedTail site.canonicalTail :=
    suffix site region following entered reference grown
  unfold Site.Outcome
  cases prepared : Record.prepare left.store left.host.writer (Field.listObjects site.entries) with
  | error issue =>
    have sameStore : left.store = right.store := by
      simpa only using congrArg (fun (cfg : State grow sig) => cfg.store) same
    have stopped := dynamic_refused_before_allocation (profile := profile) (ready := ready) (dispatch := dispatch)
      site.destination site.inst (.list site.element) site.element site.entries (.memory site.address) site.index
      left right cursor cursor checkHeadNext canonHeadNext sameStore issue prepared checkHead (keep := keep)
    exact ReachesKeeping.bind_reached rfl id (fun _ : Unit => site.checkedTail) (fun _ => site.canonicalTail) stopped later
  | ok passed =>
    cases passed
    dsimp only
    let canonBody : AddrType → Session grow sig Unit := fun width => do
      let area := layout width site.head.type
      let address := alignTo site.base area.alignment
      CanonicalTree.field Limits.spec Quirks.none cx site.destination.width site.head (.memory address)
      CanonicalTree.memory Limits.spec Quirks.none cx site.destination.width site.following (address + area.size)
    have readAt : right.ctl = cursor.control (ptrType cx >>= fun width => canonBody width >>= canonNext) := by
      rw [Site.fields, CanonicalTree.memory] at canonAt
      simpa only [cx, canonBody, Prog.bind_eq, Prog.bind_assoc] using canonAt
    let entered := { right with ctl := cursor.control (canonBody site.destination.width >>= canonNext) }
    have read : Step profile ready dispatch right .tau entered := by
      have step := Step.get (prof := profile) (hr := ready) (dispatch := dispatch)
        (k := fun store => canonBody (ptrTypeIn store cx) >>= canonNext) readAt
      have width : ptrTypeIn right.store cx = site.destination.width := widthOf site region growth
      simpa only [entered, Cursor.control, width] using step
    have sameEntered : { left with ctl := entered.ctl, host := entered.host } = entered :=
      congrArg (fun cfg : State grow sig => { cfg with ctl := entered.ctl }) same
    have canonHead : entered.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none cx
        site.destination.width site.head (.memory site.address) >>= canonHeadNext) := by
      change cursor.control (((CanonicalTree.field Limits.spec Quirks.none cx site.destination.width site.head
        (.memory site.address)).bind (fun _ => site.canonicalTail)).bind canonNext) = _
      rw [Prog.bind_assoc]
      rfl
    constructor
    · intro last seen path
      have reachedWidth := growth.memAddrType region.width
      obtain ⟨checkedInstall, canonicalInstall, paired⟩ := collection_install
        site.destination site.inst (.list site.element) site.element site.entries (.memory site.address) site.index
        left entered cursor checkHeadNext canonHeadNext sameEntered reachedWidth rfl prepared checkHead canonHead
      obtain ⟨checkedLabels, canonicalLabels, other, checkedRun, canonicalRun, related, checkedSeen, canonicalSeen⟩ :=
        path.replay paired
      have sameStore : left.store = right.store := by
        simpa only using congrArg (fun cfg : State grow sig => cfg.store) same
      have grown : keep last.store := (sameStore ▸ growth).trans checkedRun.grows
      exact ⟨_, _, other, appendSteps checkedInstall checkedRun.steps, .cons read (appendSteps canonicalInstall canonicalRun.steps),
        related, checkedSeen, canonicalSeen, grown⟩
    intro pointer last seen reached path returned
    have cut := Prefix.collection_memory site.destination site.inst (.list site.element) site.element site.entries
      (.memory site.address) site.index pointer cursor reached checkHeadNext canonHeadNext
      sameEntered growth region.width region.sized rfl prepared checkHead canonHead path returned children
    rcases cut with ⟨referenceCursor, thread, done⟩ | common
    · have continued := ReachesKeeping.bind_reached thread.symm id (fun _ : Unit => site.checkedTail)
        (fun _ => site.canonicalTail) done later
      exact .inl ⟨referenceCursor, thread, continued.prepend (.refl _) (.cons read (.refl _)) rfl⟩
    · obtain ⟨checkLabels, canonLabels, other, checks, canonical, paired, checkSeen, canonSeen⟩ := common
      exact .inr ⟨checkLabels, .tau :: canonLabels, other, checks, .cons read canonical, paired, checkSeen, canonSeen⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.NestedRecord

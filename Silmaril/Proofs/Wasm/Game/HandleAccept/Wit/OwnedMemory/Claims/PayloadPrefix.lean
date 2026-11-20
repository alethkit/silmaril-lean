module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Local.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCollection.Thms
import Silmaril.Wasm.Component.Reference.Machine.Oracle.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims

variable {E : CoreEngine} {Host Result Next : Type}
  {profile : ProfileKind} {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)}

private theorem chain {before middle after : Config E Host} {front back : List (Label E Host)}
    (left : Steps profile ready dispatch before front middle) (right : Steps profile ready dispatch middle back after) :
    Steps profile ready dispatch before (front ++ back) after := by
  induction left with
  | refl => exact right
  | cons step _ ih => exact .cons step (ih right)

private theorem silent {labels : List (Label E Host)} (allTau : ∀ label ∈ labels, label = .tau) :
    visible labels = [] := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
    have head := allTau label (List.mem_cons_self ..)
    simp only [head, visible, List.filter_cons, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun other member => allTau other (List.mem_cons_of_mem _ member))

private theorem visible_append (front back : List (Label E Host)) :
    visible (front ++ back) = visible front ++ visible back := List.filter_append ..

private theorem trace {outcome : Except TrapReason Result} {labels : List (Label E Host)}
    (valid : LocalLeafLabels outcome labels) :
    visible labels = match outcome with | .ok _ => [] | .error reason => [.trap reason] := by
  cases outcome with
  | ok _ =>
    apply silent
    intro label member
    have test := List.all_eq_true.mp valid label member
    cases label <;> simp_all
  | error reason =>
    obtain ⟨count, rfl⟩ := valid
    have prefixSilent : visible (List.replicate count (.tau : Label E Host)) = [] :=
      silent (fun label member => (List.eq_of_mem_replicate member))
    rw [visible_append, prefixSilent, List.nil_append]
    rfl

private theorem returned (value : Result) :
    Compare profile ready dispatch (pure (.ok value)) (pure value) := by
  intro left right same checkCursor canonCursor _ checkNext canonNext checkAt canonAt
  exact ⟨.returned value, [], [], left, right, .refl _, .refl _, same, rfl, checkAt, canonAt⟩

theorem sequential {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (first : Compare profile ready dispatch checked canonical)
    (checkTail : Result → P E Host (Except RecordLower.Issue Next)) (canonTail : Result → P E Host Next)
    (rest : ∀ value, Compare profile ready dispatch (checkTail value) (canonTail value)) :
    Compare profile ready dispatch
      (checked >>= fun result => match result with | .error issue => pure (.error issue) | .ok value => checkTail value)
      (canonical >>= canonTail) := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  let checkSuffix := fun (result : Except RecordLower.Issue Result) =>
    (match result with | .error issue => pure (.error issue) | .ok value => checkTail value) >>= checkNext
  let canonSuffix := fun value => canonTail value >>= canonNext
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, labels, status⟩ :=
    first left right same checkCursor canonCursor sameThread checkSuffix canonSuffix
      (by simpa only [checkSuffix, Prog.bind_eq, Prog.bind_assoc] using checkAt)
      (by simpa only [canonSuffix, Prog.bind_eq, Prog.bind_assoc] using canonAt)
  cases outcome with
  | refused issue => exact ⟨.refused issue, chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | trapped reason => exact ⟨.trapped reason, chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | returned value =>
    obtain ⟨outcome, chk', ref', left'', right'', runChk', runRef', stores', labels', status'⟩ :=
      rest value left' right' stores checkCursor canonCursor sameThread checkNext canonNext status.1 status.2
    refine ⟨outcome, chk ++ chk', ref ++ ref', left'', right'', chain runChk runChk', chain runRef runRef',
      stores', ?_, ?_⟩
    · rw [visible_append, visible_append, labels, labels']
    · cases outcome with
      | returned _ | refused _ => exact status'
      | trapped reason =>
        obtain ⟨emptyCheck, emptyCanon, leading, last⟩ := status'
        refine ⟨emptyCheck, emptyCanon, visible ref ++ leading, ?_⟩
        rw [visible_append, last, List.append_assoc]

private theorem mapResult {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (compare : Compare profile ready dispatch checked canonical) (resultMap : Result → Next)
    (issueMap : RecordLower.Issue → RecordLower.Issue) :
    Compare profile ready dispatch (do return ((← checked).map resultMap).mapError issueMap)
      (do return resultMap (← canonical)) := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, labels, status⟩ :=
    compare left right same checkCursor canonCursor sameThread
      (fun result => checkNext ((result.map resultMap).mapError issueMap)) (fun value => canonNext (resultMap value))
      (by simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using checkAt) (by
        simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using canonAt)
  cases outcome with
  | returned value => exact ⟨.returned (resultMap value), chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | refused issue => exact ⟨.refused (issueMap issue), chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | trapped reason => exact ⟨.trapped reason, chk, ref, left', right', runChk, runRef, stores, labels, status⟩

private theorem map_id (result : Except RecordLower.Issue Result) : result.map id = result := by
  cases result <;> rfl

private theorem mapError_id (result : Except RecordLower.Issue Result) : result.mapError id = result := by
  cases result <;> rfl

private theorem mapIssue {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (compare : Compare profile ready dispatch checked canonical) (issueMap : RecordLower.Issue → RecordLower.Issue) :
    Compare profile ready dispatch (do return (← checked).mapError issueMap) canonical := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, labels, status⟩ :=
    compare left right same checkCursor canonCursor sameThread (fun result => checkNext (result.mapError issueMap)) canonNext
      (by simpa only [Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using checkAt) canonAt
  cases outcome with
  | returned value => exact ⟨.returned value, chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | refused issue => exact ⟨.refused (issueMap issue), chk, ref, left', right', runChk, runRef, stores, labels, status⟩
  | trapped reason => exact ⟨.trapped reason, chk, ref, left', right', runChk, runRef, stores, labels, status⟩

private def ClosedOp (profile : ProfileKind) : Op E Host → Prop
  | .choose choice => ∃ answer, Allowed profile choice answer
  | .get | .modify _ | .currentThread | .trap _ => True
  | _ => False

private theorem pairedTau {left right left' right' : Config E Host}
    {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (checkStep : Step profile ready dispatch left .tau left') (canonStep : Step profile ready dispatch right .tau right')
    (tails : Reaches profile ready dispatch left' right' checkCursor canonCursor checkNext canonNext) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, chk, ref, checkEnd, canonEnd, runChk, runRef, stores, labels, status⟩ := tails
  exact ⟨outcome, .tau :: chk, .tau :: ref, checkEnd, canonEnd, .cons checkStep runChk,
    .cons canonStep runRef, stores, labels, status⟩

private theorem compareClosed {body : P E Host Result} (closed : Prog.Every (ClosedOp profile) body) :
    Compare profile ready dispatch (do return .ok (← body)) body := by
  induction closed with
  | pure value => exact returned value
  | @op operation next admitted _ inductionHypothesis =>
    intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
    cases operation with
    | get =>
      let left' := { left with ctl := checkCursor.control ((do return Except.ok (← next left.store)) >>= checkNext) }
      let right' := { right with ctl := canonCursor.control (next right.store >>= canonNext) }
      have checkStep : Step profile ready dispatch left .tau left' := .get checkAt
      have canonStep : Step profile ready dispatch right .tau right' := .get canonAt
      refine pairedTau checkStep canonStep ?_
      refine inductionHypothesis right.store left' right' same checkCursor canonCursor sameThread checkNext canonNext ?_ rfl
      exact congrArg (fun value : (Eff E Host).Resp .get =>
        checkCursor.control ((do return Except.ok (← next value)) >>= checkNext)) same
    | modify update =>
      exact pairedTau (.modify checkAt) (.modify canonAt)
        (inductionHypothesis () _ _ (congrArg update same) checkCursor canonCursor sameThread checkNext canonNext rfl rfl)
    | currentThread =>
      let left' := { left with ctl := checkCursor.control ((do return Except.ok (← next checkCursor.thread)) >>= checkNext) }
      let right' := { right with ctl := canonCursor.control (next canonCursor.thread >>= canonNext) }
      have checkStep : Step profile ready dispatch left .tau left' := .currentThread checkAt
      have canonStep : Step profile ready dispatch right .tau right' := .currentThread canonAt
      refine pairedTau checkStep canonStep ?_
      refine inductionHypothesis canonCursor.thread left' right' same checkCursor canonCursor sameThread
        checkNext canonNext ?_ rfl
      exact congrArg (fun value : (Eff E Host).Resp .currentThread =>
        checkCursor.control ((do return Except.ok (← next value)) >>= checkNext)) sameThread
    | trap reason =>
      refine ⟨.trapped reason, [.trap reason], [.trap reason], StepDefs.trapCfg left, StepDefs.trapCfg right,
        .cons (.trap checkAt) (.refl _), .cons (.trap canonAt) (.refl _), ?_, rfl, rfl, rfl, [], rfl⟩
      exact congrArg StepDefs.lockdownSt same
    | choose choice =>
      obtain ⟨answer, allowed⟩ := admitted
      let left' := { left with ctl := checkCursor.control ((do return Except.ok (← next answer)) >>= checkNext) }
      let right' := { right with ctl := canonCursor.control (next answer >>= canonNext) }
      have checkStep : Step profile ready dispatch left (.choice choice answer) left' := .choose answer checkAt allowed
      have canonStep : Step profile ready dispatch right (.choice choice answer) right' := .choose answer canonAt allowed
      obtain ⟨outcome, chk, ref, checkEnd, canonEnd, runChk, runRef, stores, labels, status⟩ :=
        inductionHypothesis answer left' right' same checkCursor canonCursor sameThread checkNext canonNext rfl rfl
      let chosen : Label E Host := .choice choice answer
      refine ⟨outcome, chosen :: chk, chosen :: ref, checkEnd, canonEnd,
        .cons checkStep runChk, .cons canonStep runRef, stores, ?_, ?_⟩
      · exact congrArg (chosen :: ·) labels
      · cases outcome with
        | returned _ | refused _ => exact status
        | trapped reason =>
          obtain ⟨checkEmpty, canonEmpty, leading, last⟩ := status
          exact ⟨checkEmpty, canonEmpty, chosen :: leading, congrArg (chosen :: ·) last⟩
    | _ => contradiction

private theorem closedLowerFloat (profile : ProfileKind) (kind : FloatType) (bits : BitVec kind.width) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile) (lowerFloat kind bits) := by
  unfold lowerFloat
  split
  · exact .op ⟨firstNan profile kind bits, firstNan_allowed profile kind bits⟩ (fun _ => .pure _)
  · exact .pure _

private theorem encodeCoercion (profile : ProfileKind) (kind : FloatType) (bits : BitVec kind.width) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile) (encodeFloat kind bits) :=
  (closedLowerFloat profile kind bits).bind (fun _ => .pure _)

private theorem coerceWord (profile : ProfileKind) (haveType wantType : CoreType) (word : FlatValue) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile) (coerceLower haveType wantType word) := by
  unfold coerceLower
  split
  · exact (encodeCoercion profile .f32 _).bind (fun _ => .pure _)
  · exact .pure _
  · exact (encodeCoercion profile .f32 _).bind (fun _ => .pure _)
  · exact (encodeCoercion profile .f64 _).bind (fun _ => .pure _)
  · exact .pure _

private theorem coerceWords (profile : ProfileKind) (haves wants : List CoreType) (words : List FlatValue) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile) (coerceLowerSlots haves wants words) := by
  induction haves generalizing wants words with
  | nil => exact .pure _
  | cons haveType remaining ih =>
    cases words with
    | nil => cases wants <;> exact .pure _
    | cons word remainingWords =>
      cases wants with
      | nil => exact .op trivial (fun impossible => nomatch impossible)
      | cons wantType remainingWants =>
        exact (coerceWord profile haveType wantType word).bind fun _ =>
          (ih remainingWants remainingWords).bind fun _ => .pure _

private theorem variantTail (count : Nat) (wanted : List CoreType) (tag : Nat) (haves : List CoreType)
    (words : List FlatValue) :
    Compare profile ready dispatch
      (do return .ok (← lowerFlatVariantWith count wanted tag haves (pure words)))
      (lowerFlatVariantWith count wanted tag haves (pure words)) := by
  apply compareClosed
  unfold lowerFlatVariantWith
  split
  · exact (coerceWords profile haves wanted words).bind (fun _ => .pure _)
  · exact .op trivial (fun impossible => nomatch impossible)

private theorem localGet : Prog.Every (ClosedOp (E := E) (Host := Host) profile) getStore := .op trivial (fun _ => .pure _)

private theorem closedInt (cx : LiftLowerContext E) (number : Int) (ptr bytes : Nat) (signed : Bool := false) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile) (storeInt cx number ptr bytes signed) := by
  unfold storeInt writeMem memAddr
  have addressLocal : Prog.Every (ClosedOp (E := E) (Host := Host) profile) (orTrap .noMemory cx.opts.memory) := by
    cases cx.opts.memory
    · exact .op trivial (fun impossible => nomatch impossible)
    · exact .pure _
  refine addressLocal.bind fun address => localGet.bind fun store => ?_
  split
  · exact .op trivial (fun impossible => nomatch impossible)
  · exact .op trivial (fun _ => .pure _)

private theorem closedStorePrim (cx : LiftLowerContext E) (primitive : WIT.Primitive) (value : Value.Val)
    (nonString : primitive ≠ .string) (ptr : Nat) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile) (storePrim Limits.spec Quirks.none cx primitive value ptr) := by
  unfold storePrim
  split
  · exact closedInt cx _ ptr _
  · exact (encodeCoercion profile .f32 _).bind (fun _ => closedInt cx _ ptr _)
  · exact (encodeCoercion profile .f64 _).bind (fun _ => closedInt cx _ ptr _)
  · exact closedInt cx _ ptr _
  · contradiction
  · split
    · exact closedInt cx _ ptr _ _
    · exact .op trivial (fun impossible => nomatch impossible)
  · exact .op trivial (fun impossible => nomatch impossible)

private theorem closedFlatPrim (cx : LiftLowerContext E) (width : AddrType) (primitive : WIT.Primitive)
    (value : Value.Val) (nonString : primitive ≠ .string) :
    Prog.Every (ClosedOp (E := E) (Host := Host) profile) (lowerFlatPrim Limits.spec Quirks.none cx width primitive value) := by
  unfold lowerFlatPrim
  split
  · exact .pure _
  · exact (closedLowerFloat profile .f32 _).bind (fun _ => .pure _)
  · exact (closedLowerFloat profile .f64 _).bind (fun _ => .pure _)
  · exact .pure _
  · contradiction
  · split
    · exact .pure _
    · exact .op trivial (fun impossible => nomatch impossible)
  · exact .op trivial (fun impossible => nomatch impossible)

private theorem variantHead (cx : LiftLowerContext E) (count : Nat) (alignment : Alignment) (tag ptr : Nat) :
    Compare profile ready dispatch
      (do return .ok (← storeVariantHead cx count alignment tag ptr))
      (storeVariantHead cx count alignment tag ptr) :=
  compareClosed ((closedInt cx tag ptr (discSize count)).bind (fun _ => .pure _))

private theorem descriptor (cx : LiftLowerContext E) (width : AddrType) (ptr count : Nat) (output : Lower.Output) :
    Compare profile ready dispatch (do return .ok (← ListLower.publish cx width ptr count output))
      (ListLower.publish cx width ptr count output) := by
  cases output with
  | flat => exact returned _
  | memory dest =>
    apply compareClosed
    have localSize : Prog.Every (ClosedOp (E := E) (Host := Host) profile) (ptrSize cx) :=
      localGet.bind (fun _ => .pure _)
    exact localSize.bind (fun size => (closedInt cx ptr dest size).bind (fun _ => closedInt cx count (dest + size) size))

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {scheduledReady : HostReady (HostState sig)}
  {scheduledDispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

theorem handle (destination : RecordDestination) (inst : InstId) (item : Field) (isHandle : CanonicalHandle item)
    (index : Nat) (output : Lower.Output) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.checkedLeaf recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item index output)
      (CanonicalTree.leaf Limits.spec Quirks.none (destination.context inst) destination.width item output) := by
  intro left right same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  rcases checkCursor with ⟨thread, checkFrames, checkRest⟩
  rcases canonCursor with ⟨otherThread, canonFrames, canonRest⟩
  change thread = otherThread at sameThread
  subst otherThread
  have paired := RecordDestination.compare_handle_leaf (profile := profile) (ready := scheduledReady)
    (dispatch := scheduledDispatch) same destination inst item isHandle index output checkNext canonNext checkAt canonAt
  cases verdict : liveLeafPlan left.store left.host.writer index item with
  | error issue =>
    rw [verdict] at paired
    obtain ⟨labels, allTau, steps⟩ := paired
    exact ⟨.refused issue, labels, [], _, right, steps, .refl right, same, silent allTau, rfl⟩
  | ok plan =>
    rw [verdict] at paired
    obtain ⟨reached, outcome, leading, chk, ref, allTau, checkTrace, canonTrace, checkRun, canonRun⟩ := paired
    have labels : visible (leading ++ chk) = visible ref := by
      cases outcome <;> rw [visible_append, silent allTau, List.nil_append, trace checkTrace, trace canonTrace]
    cases outcome with
    | ok value => exact ⟨.returned value, _, _, _, _, checkRun, canonRun, rfl, labels, rfl, rfl⟩
    | error reason =>
      exact ⟨.trapped reason, _, _, _, _, checkRun, canonRun, rfl, labels, rfl, rfl, [], trace canonTrace⟩

private theorem guardedTail {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (first : Compare profile ready dispatch checked canonical) (mapIssue : RecordLower.Issue → RecordLower.Issue)
    (checkTail : Result → P E Host (Except RecordLower.Issue Next)) (canonTail : Result → P E Host Next)
    (later : ∀ value, Compare profile ready dispatch (checkTail value) (canonTail value)) :
    Compare profile ready dispatch
      (checked >>= fun result => match result with
        | .error issue => pure (.error (mapIssue issue)) | .ok value => checkTail value)
      (canonical >>= canonTail) := by
  have compared := sequential (mapResult first id mapIssue) checkTail canonTail later
  simp only [map_id, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] at compared ⊢
  convert compared using 2 <;> try rfl
  funext verdict
  cases verdict <;> rfl

private theorem readWidth (cx : LiftLowerContext E) (left right : Config E Host) (width : AddrType)
    (reachedWidth : ptrTypeIn right.store cx = width) (checked : P E Host (Except RecordLower.Issue Result))
    (canonical : AddrType → P E Host Result) (tail : Compare profile ready dispatch checked (canonical width)) :
    CompareAt profile ready dispatch left right checked (ptrType cx >>= canonical) := by
  intro same checkCursor canonCursor sameThread checkNext canonNext checkAt canonAt
  let entered := { right with ctl := canonCursor.control (canonical width >>= canonNext) }
  have step : Step profile ready dispatch right .tau entered := by
    have read := Step.get (prof := profile) (hr := ready) (dispatch := dispatch)
      (k := fun store => canonical (ptrTypeIn store cx) >>= canonNext) canonAt
    simpa only [entered, Cursor.control, reachedWidth] using read
  obtain ⟨outcome, chk, ref, checkEnd, canonEnd, runChk, runRef, stores, labels, status⟩ :=
    tail left entered same checkCursor canonCursor sameThread checkNext canonNext checkAt rfl
  exact ⟨outcome, chk, .tau :: ref, checkEnd, canonEnd, runChk, .cons step runRef, stores, labels, status⟩

theorem memorySum (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (arms : List (Option TypeOf)) (tag index ptr : Nat) (selected : Option Field)
    (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn right.store (destination.context inst) = destination.width)
    (child : ∀ item address, selected = some item → Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item 0 (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    CompareAt profile scheduledReady scheduledDispatch left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) index (.memory ptr))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) (.memory ptr)) := by
  rw [Record.Effects.field, CanonicalTree.field]
  apply readWidth _ left right destination.width width
  let head := storeVariantHead (σ := HostState sig) (destination.context (grow := grow) inst) arms.length
    (maxCaseAlignment (arms.map (layoutOption destination.width))) tag ptr
  have compared : Compare profile scheduledReady scheduledDispatch (do return .ok (← head)) head :=
    variantHead (destination.context inst) arms.length (maxCaseAlignment (arms.map (layoutOption destination.width))) tag ptr
  cases selected with
  | none =>
    have composed := sequential compared (fun _ => pure (.ok ())) (fun _ => pure ()) (fun _ => returned ())
    simpa only [Lower.Output.Result, head, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using composed
  | some active =>
    have composed := sequential compared
      (fun address => do
        return (← Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
          destination.width active 0 (.memory address)).mapError (.nested index))
      (fun address => CanonicalTree.field Limits.spec Quirks.none (destination.context inst)
        destination.width active (.memory address))
      (fun address => mapIssue (child active address rfl) (.nested index))
    simpa only [Lower.Output.Result, head, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using composed

theorem memoryHandleLeaf (destination : RecordDestination) (inst : InstId) (field : Field) (index ptr : Nat)
    (fragment : CanonicalHandle field) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        field index (.memory ptr))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width field (.memory ptr)) := by
  cases field with
  | owner _ | endpoint _ _ _ | context _ =>
    rw [Record.Effects.field, CanonicalTree.field]
    exact handle destination inst _ fragment index (.memory ptr)
  | _ => exact False.elim fragment

theorem memoryHandleRoot (destination : RecordDestination) (inst : InstId) (field : Field) (index ptr : Nat)
    (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn right.store (destination.context inst) = destination.width) (fragment : MemoryHandleRoot field) :
    CompareAt profile scheduledReady scheduledDispatch left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        field index (.memory ptr))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width field (.memory ptr)) := by
  cases field with
  | owner _ | endpoint _ _ _ | context _ => exact memoryHandleLeaf destination inst _ index ptr (by trivial) left right
  | sum type arms tag selected =>
    apply memorySum destination inst type arms tag index ptr selected left right width
    cases selected with
    | none => intro item address impossible; contradiction
    | some active =>
      intro item address same
      cases same
      exact memoryHandleLeaf destination inst active 0 address fragment
  | _ => exact False.elim fragment

theorem flatSum (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (arms : List (Option TypeOf)) (tag index : Nat) (selected : Option Field) (valid : tag < arms.length)
    (child : ∀ item, selected = some item → Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item 0 .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item .flat)) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) index .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) .flat) := by
  cases selected with
  | none =>
    rw [Record.Effects.field, CanonicalTree.field]
    exact variantTail arms.length ((flatten destination.width type).drop 1) tag [] []
  | some item =>
    rw [Record.Effects.field, CanonicalTree.field]
    let wanted := (flatten destination.width type).drop 1
    let haves := flatten destination.width item.type
    have placed := guardedTail (child item rfl) (.nested index)
      (fun words => do return .ok (← lowerFlatVariantWith arms.length wanted tag haves (pure words)))
      (fun words => lowerFlatVariantWith arms.length wanted tag haves (pure words))
      (variantTail arms.length wanted tag haves)
    simp only [Lower.Output.Result, lowerFlatVariantWith, valid, ↓reduceIte, Prog.bind_eq, Prog.bind_assoc,
      Prog.pure_eq, Prog.pure_bind'] at placed ⊢
    convert placed using 2
    funext verdict
    cases verdict <;> rfl

mutual
theorem flatField (destination : RecordDestination) (inst : InstId) (item : Field)
    (fragment : HandleField item) (index : Nat) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item index .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item .flat) := by
  cases item with
  | aggregate type children | fixed type size children =>
    simp only [HandleField, HandleFieldWhere] at fragment
    have compared := flatFields destination inst children fragment 0
    rw [Record.Effects.field, CanonicalTree.field]
    simpa only [Lower.Output.Result, map_id, id_eq, Prog.bind_eq, Prog.pure_eq, Prog.bind_pure] using
      mapResult compared id (.nested index)
  | owner _ | endpoint _ _ _ | context _ =>
    rw [Record.Effects.field, CanonicalTree.field]
    exact handle destination inst _ fragment index .flat
  | sum type arms tag selected =>
    simp only [HandleField, HandleFieldWhere] at fragment
    apply flatSum destination inst type arms tag index selected fragment.1
    cases selected with
    | none => intro item impossible; contradiction
    | some active =>
      intro item same
      cases same
      exact flatField destination inst active fragment.2 0
  | data _ _ | dynamic _ _ _ => exact False.elim fragment
termination_by structural item

theorem flatFields (destination : RecordDestination) (inst : InstId) (items : List Field)
    (fragment : HandleFieldsWhere Nat.lt items) (index : Nat) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.flat recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width items index)
      (CanonicalTree.flat Limits.spec Quirks.none (destination.context inst) destination.width items) := by
  cases items with
  | nil => rw [Record.Effects.flat, CanonicalTree.flat]; exact returned []
  | cons child rest =>
    rw [HandleFieldsWhere] at fragment
    rw [Record.Effects.flat, CanonicalTree.flat]
    have first := flatField destination inst child fragment.1 index
    have later := flatFields destination inst rest fragment.2 (index + 1)
    have composed := sequential first _ _ (fun words => by
      let headWords : List FlatValue := words
      simpa only [mapError_id] using mapResult later (headWords ++ ·) id)
    convert composed using 2 <;> try rfl
    funext verdict
    cases verdict <;> rfl
termination_by structural items
end

theorem certifyField {field : Field} {type : TypeOf} (layout : Field.LayoutMatches field type)
    (fragment : HandleShape field) : HandleField field := by
  exact Field.LayoutMatches.rec
    (motive_1 := fun item _ _ => HandleShape item → HandleField item)
    (motive_2 := fun fields _ _ => HandleFieldsWhere (fun _ _ => True) fields → HandleFieldsWhere Nat.lt fields)
    (motive_3 := fun fields _ _ => HandleFieldsWhere (fun _ _ => True) fields → HandleFieldsWhere Nat.lt fields)
    (motive_4 := fun arm _ _ => HandleArmWhere (fun _ _ => True) arm → HandleArmWhere Nat.lt arm)
    (fun _ bad => False.elim bad)
    (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
    (fun _ children => children) (fun _ children => children) (fun _ _ children => children)
    (fun _ _ bad => False.elim bad) (fun _ _ bad => False.elim bad)
    (fun found _ active shape => ⟨(List.getElem?_eq_some_iff.mp found).1, active shape.2⟩)
    (fun _ => ⟨show 0 < 2 by decide, trivial⟩)
    (fun _ active shape => ⟨show 1 < 2 by decide, active shape.2⟩)
    (fun _ active shape => ⟨show 0 < 2 by decide, active shape.2⟩)
    (fun _ active shape => ⟨show 1 < 2 by decide, active shape.2⟩)
    (fun _ => trivial) (fun _ _ child rest shape => ⟨child shape.1, rest shape.2⟩)
    (fun _ => trivial) (fun _ _ child rest shape => ⟨child shape.1, rest shape.2⟩)
    (fun _ => trivial) (fun _ child => child) layout fragment

private theorem prependCheck {left entered right : Config E Host} {labels : List (Label E Host)}
    {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (entry : Steps profile ready dispatch left labels entered) (allTau : ∀ label ∈ labels, label = .tau)
    (continued : Reaches profile ready dispatch entered right checkCursor canonCursor checkNext canonNext) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, observations, status⟩ := continued
  refine ⟨outcome, labels ++ chk, ref, left', right', chain entry runChk, runRef, stores, ?_, ?_⟩
  · rw [visible_append, silent allTau, List.nil_append, observations]
  · cases outcome <;> exact status

private theorem prependCanon {left entered right : Config E Host} {labels : List (Label E Host)}
    {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (entry : Steps profile ready dispatch right labels entered) (allTau : ∀ label ∈ labels, label = .tau)
    (continued : Reaches profile ready dispatch left entered checkCursor canonCursor checkNext canonNext) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, chk, ref, left', right', runChk, runRef, stores, observations, status⟩ := continued
  refine ⟨outcome, chk, labels ++ ref, left', right', runChk, chain entry runRef, stores, ?_, ?_⟩
  · rw [visible_append, silent allTau, List.nil_append, observations]
  · cases outcome with
    | returned _ | refused _ => exact status
    | trapped _ => simpa only [visible_append, silent allTau, List.nil_append] using status

theorem prepend {left left' right right' : Config E Host} {checkLabels canonLabels : List (Label E Host)}
    {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (lhs : Steps profile ready dispatch left checkLabels left') (rhs : Steps profile ready dispatch right canonLabels right')
    (seen : visible checkLabels = visible canonLabels)
    (rest : Reaches profile ready dispatch left' right' checkCursor canonCursor checkNext canonNext) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext := by
  obtain ⟨outcome, checkTail, canonTail, checkEnd, canonEnd, checkRun, canonRun, stores, same, status⟩ := rest
  refine ⟨outcome, checkLabels ++ checkTail, canonLabels ++ canonTail, checkEnd, canonEnd,
    chain lhs checkRun, chain rhs canonRun, stores, ?_, ?_⟩
  · rw [visible_append, visible_append, seen, same]
  · cases outcome with
    | returned _ | refused _ => exact status
    | trapped _ =>
      obtain ⟨checkDone, canonDone, leading, trapLabel⟩ := status
      exact ⟨checkDone, canonDone, visible canonLabels ++ leading, by rw [visible_append, trapLabel, List.append_assoc]⟩

private theorem collectionElements (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (stride ptr index : Nat) (compared : ∀ item ∈ entries, ∀ address pos,
      Compare profile scheduledReady scheduledDispatch
        (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
          item pos (.memory address))
        (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    Compare profile scheduledReady scheduledDispatch
      (Record.Effects.elements recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        entries stride ptr index)
      (CanonicalTree.elements Limits.spec Quirks.none (destination.context inst) destination.width entries
        .value stride ptr) := by
  induction entries generalizing ptr index with
  | nil => rw [Record.Effects.elements, CanonicalTree.elements]; exact returned ()
  | cons item rest ih =>
    rw [Record.Effects.elements, CanonicalTree.elements]
    have head := compared item (List.mem_cons_self ..) ptr index
    have tail := ih (ptr + stride) (index + 1)
      (fun entry member => compared entry (List.mem_cons_of_mem _ member))
    have paired := sequential head _ _ (fun _ => tail)
    convert paired using 2 <;> try rfl
    funext verdict
    cases verdict with
    | ok value => cases value; rfl
    | error _ => rfl

private theorem collectionTail (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index ptr : Nat)
    (compared : ∀ item ∈ entries, ∀ address pos, Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        item pos (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    Compare profile scheduledReady scheduledDispatch
      (checkedCollectionTail destination inst entries area index output ptr (.ok ()))
      (canonicalCollectionTail destination inst entries area output ptr) := by
  let publish := (ListLower.publish (destination.context inst) destination.width ptr entries.length output : Session grow sig output.Result)
  have paired := guardedTail (collectionElements destination inst entries area.size ptr 0 compared) (.nested index)
    (fun _ => do return .ok (← publish)) (fun _ => publish)
    (fun _ => descriptor (destination.context inst) destination.width ptr entries.length output)
  unfold checkedCollectionTail canonicalCollectionTail
  convert paired using 2
  funext verdict
  cases verdict with
  | ok value => cases value; rfl
  | error _ => rfl

theorem collectionReturnAt (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    (left right : Config (core3 grow) (HostState sig)) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkResume canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (paired : HostFrame.Paired checkResume canonResume left right) (sameThread : checkCursor.thread = canonCursor.thread)
    (leftAt : left.ctl = { checkCursor with frames := .prog checkResume :: checkCursor.frames }.control (pure (.nat pointer)))
    (rightAt : right.ctl = { canonCursor with frames := .prog canonResume :: canonCursor.frames }.control (pure (.nat pointer)))
    (checkBody : checkResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : canonResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    {bytes : Nat} (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (compared : CollectionTailAt profile scheduledReady scheduledDispatch destination inst entries area output index
      pointer bytes left right) :
    Reaches profile scheduledReady scheduledDispatch left right checkCursor canonCursor checkNext canonNext := by
  rcases checkCursor with ⟨thread, checkFrames, checkRest⟩
  rcases canonCursor with ⟨otherThread, canonFrames, canonRest⟩
  change thread = otherThread at sameThread
  subst otherThread
  let checkSuffix := fun ptr live => checkedCollectionTail destination inst entries area index output ptr live >>= checkNext
  let canonSuffix := fun ptr => canonicalCollectionTail destination inst entries area output ptr >>= canonNext
  have prefixed := destination.paired_range_recheck (profile := profile) (ready := scheduledReady)
    (dispatch := scheduledDispatch) paired inst area entries.length pointer (Field.listObjects entries)
    checkSuffix canonSuffix checkBody canonBody leftAt rightAt sized
  have finishTrap (reason : TrapReason)
      (leftRun : ∃ count, Steps profile scheduledReady scheduledDispatch left (List.replicate count .tau ++ [.trap reason])
        (StepDefs.trapCfg left))
      (rightRun : ∃ count, Steps profile scheduledReady scheduledDispatch right (List.replicate count .tau ++ [.trap reason])
        (StepDefs.trapCfg right)) :
      Reaches profile scheduledReady scheduledDispatch left right ⟨thread, checkFrames, checkRest⟩
        ⟨thread, canonFrames, canonRest⟩ checkNext canonNext := by
    obtain ⟨leftCount, checkSteps⟩ := leftRun
    obtain ⟨rightCount, canonSteps⟩ := rightRun
    have hide (count : Nat) : visible (List.replicate count .tau ++ [.trap reason] : List (Label (core3 grow) (HostState sig))) =
        [.trap reason] := trace (outcome := (.error reason : Except TrapReason Unit)) ⟨count, rfl⟩
    exact ⟨.trapped reason, _, _, _, _, checkSteps, canonSteps, congrArg StepDefs.lockdownSt paired.data.1,
      (hide leftCount).trans (hide rightCount).symm, rfl, rfl, [], hide rightCount⟩
  dsimp only at prefixed
  by_cases aligned : pointer ≠ alignTo pointer area.alignment
  · simp only [ite_eq_left aligned] at prefixed
    exact finishTrap .unalignedPointer prefixed.1 prefixed.2
  by_cases fits : pointer + entries.length * area.size ≤ bytes
  · simp only [ite_eq_right aligned, ite_eq_left fits] at prefixed
    obtain ⟨⟨checkLabels, checkSilent, checkSteps⟩, ⟨canonLabels, canonSilent, canonSteps⟩⟩ := prefixed
    cases verdict : Record.prepare left.store left.host.writer (Field.listObjects entries) with
    | ok passed =>
      cases passed
      rw [verdict] at checkSteps
      let checkEntered := { left with ctl := Cursor.control ⟨thread, checkFrames, checkRest⟩ (checkSuffix pointer (.ok ())) }
      let canonEntered := { right with ctl := Cursor.control ⟨thread, canonFrames, canonRest⟩ (canonSuffix pointer) }
      have continued := compared (Classical.not_not.mp aligned) fits verdict checkEntered canonEntered rfl rfl rfl rfl
        paired.data.1 ⟨thread, checkFrames, checkRest⟩ ⟨thread, canonFrames, canonRest⟩ rfl checkNext canonNext rfl rfl
      exact prependCheck checkSteps checkSilent (prependCanon canonSteps canonSilent continued)
    | error issue =>
      rw [verdict] at checkSteps
      cases issue <;> exact ⟨.refused _, checkLabels, canonLabels, _, _, checkSteps, canonSteps,
        paired.data.1, (silent checkSilent).trans (silent canonSilent).symm, rfl⟩
  · simp only [ite_eq_right aligned, ite_eq_right fits] at prefixed
    exact finishTrap .outOfBounds prefixed.1 prefixed.2

theorem collectionTailFromChildren (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer bytes : Nat) (left right : Config (core3 grow) (HostState sig))
    (compared : ∀ item ∈ entries, ∀ address pos, Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        item pos (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    CollectionTailAt profile scheduledReady scheduledDispatch destination inst entries area output index pointer bytes left right :=
  fun _ _ _ checked canonical _ _ _ _ => collectionTail destination inst entries area output index pointer compared checked canonical

theorem collectionCallback (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index : Nat)
    {left right last : Config (core3 grow) (HostState sig)} {labels}
    (callback : CoreGrowthSteps profile scheduledReady scheduledDispatch left labels last)
    (destinationChecked : destination.check left.store = .ok ()) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {checkResume canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (paired : HostFrame.Paired checkResume canonResume left right)
    (checkBody : ∀ pointer, checkResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : ∀ pointer, canonResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    (compared : ∀ item ∈ entries, ∀ address pos, Compare profile scheduledReady scheduledDispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        item pos (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    (∃ other, CoreGrowthSteps profile scheduledReady scheduledDispatch right labels other ∧ HostFrame.Paired checkResume canonResume last other) ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧ CoreGrowthSteps profile scheduledReady scheduledDispatch left leading atLeft ∧
      CoreGrowthSteps profile scheduledReady scheduledDispatch right leading atRight ∧ HostFrame.Paired checkResume canonResume atLeft atRight ∧
      Step profile scheduledReady scheduledDispatch atLeft label afterLeft ∧ Step profile scheduledReady scheduledDispatch atRight label afterRight ∧
      CoreGrowthSteps profile scheduledReady scheduledDispatch afterLeft trailing last ∧
      ((∃ alternate, HostFrame.ReadCut atLeft atRight.host label afterLeft alternate ∧
          ReturnFrame.Paired checkResume canonResume alternate afterRight) ∨
       (∃ thread value frames rest,
          (∀ pointer, value ≠ .nat pointer) ∧
          atLeft.ctl = ⟨thread, .prog (.pure value), .prog checkResume :: frames⟩ :: rest ∧
          ReturnFrame.Returned checkResume canonResume (HostFrame.replace atLeft atRight.host) atRight label
            (HostFrame.replace afterLeft atRight.host) afterRight) ∨
       (∃ (pointer : Nat) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig)),
          atLeft.ctl = { checkCursor with frames := .prog checkResume :: checkCursor.frames }.control (pure (.nat pointer)) ∧
          atRight.ctl = { canonCursor with frames := .prog canonResume :: canonCursor.frames }.control (pure (.nat pointer)) ∧
          canonCursor.thread = checkCursor.thread ∧
          Reaches profile scheduledReady scheduledDispatch left right checkCursor canonCursor checkNext canonNext))) := by
  rcases HostFrame.paired_growing_steps paired callback with replayed |
    ⟨leading, label, trailing, atLeft, atRight, afterLeft, afterRight, split, lhs, rhs, reached, cut, leftStep, rightStep, suffix⟩
  · exact .inl replayed
  refine .inr ⟨leading, label, trailing, atLeft, atRight, afterLeft, afterRight, split,
    lhs, rhs, reached, leftStep, rightStep, suffix, ?_⟩
  cases cut with
  | read differs otherAligned => exact .inl ⟨_, differs, otherAligned⟩
  | returned popped =>
    obtain ⟨thread, value, leftFrames, rightFrames, leftRest, rightRest, atChecked, atCanonical⟩ := popped.inputs
    cases value with
    | unit | flat _ | vals _ | optVals _ | cancel _ | thread _ | invoked _ _ | items _ =>
      exact .inr (.inl ⟨thread, _, leftFrames, leftRest, by simp, atChecked, popped⟩)
    | nat pointer =>
      let checkCursor : Cursor (E := core3 grow) (HostState sig) := ⟨thread, leftFrames, leftRest⟩
      let canonCursor : Cursor (E := core3 grow) (HostState sig) := ⟨thread, rightFrames, rightRest⟩
      have region := lhs.linked_region (destination.context inst) (start := 0) (length := 0)
        rfl (destination.check_width left.store destinationChecked) sized (by simp)
      obtain ⟨_, reachedSize, _, _⟩ := region.2.2
      have continued := collectionReturnAt destination inst entries area output index pointer atLeft atRight
        checkCursor canonCursor checkNext canonNext checkResume canonResume reached rfl atChecked atCanonical
        (checkBody pointer) (canonBody pointer) reachedSize
        (collectionTailFromChildren destination inst entries area output index pointer _ atLeft atRight compared)
      exact .inr (.inr ⟨pointer, checkCursor, canonCursor, atChecked, atCanonical, rfl,
        prepend lhs.steps rhs.steps rfl continued⟩)

theorem collectionInstall (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (left right : Config (core3 grow) (HostState sig)) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    {initial labels} (prefixRun : CoreGrowthSteps profile scheduledReady scheduledDispatch initial labels right)
    (checkedDestination : destination.check initial.store = .ok ())
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
    let checkCall := collectionEntry destination inst area entries.length scheduledDispatch left cursor checkResume
    let canonCall := collectionEntry destination inst area entries.length scheduledDispatch right cursor canonResume
    Machine.Steps profile scheduledReady scheduledDispatch left [.tau, .tau, .tau] checkCall ∧
    Machine.Steps profile scheduledReady scheduledDispatch right [.tau, .tau] canonCall ∧
    HostFrame.Paired checkResume canonResume checkCall canonCall := by
  let cx := destination.context (grow := grow) inst
  let area := layout destination.width element
  have reached : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width :=
    prefixRun.grows.memAddrType (destination.check_width initial.store checkedDestination)
  have width : ptrTypeIn right.store (destination.context inst) = destination.width := by
    simp [ptrTypeIn, RecordDestination.context, CanonOpts.ptrType, reached]
  let liveObjects := Field.listObjects entries
  let checkedTail := fun ptr => do
    let live ← Record.Effects.reserve recordClaims liveObjects
    checkedCollectionTail destination inst entries area index output ptr live >>= checkNext
  let preflightBranch := fun (verdict : Except RecordLower.Issue Unit) =>
    (match verdict with
     | .error (.preflight issue) => pure (.error (.field index (.beforeAllocation issue)))
     | .error issue => pure (.error (.nested index issue))
     | .ok () => do
        let ptr ← allocateListRange cx area entries.length
        let live ← Record.Effects.reserve recordClaims liveObjects
        checkedCollectionTail destination inst entries area index output ptr live) >>= checkNext
  have checkRead : left.ctl = cursor.control (.op .get fun store => .op .hostGet fun host =>
      preflightBranch (Record.prepare store host.writer liveObjects)) := by
    rw [Record.Effects.field] at checkAt
    exact checkAt
  let checkEntered := { left with ctl := cursor.control (preflightBranch (Record.prepare left.store left.host.writer liveObjects)) }
  have checkSteps : Machine.Steps profile scheduledReady scheduledDispatch left [.tau, .tau] checkEntered :=
    .cons (.get checkRead) (.cons (.hostGet rfl) (.refl _))
  have checkAlloc : checkEntered.ctl = cursor.control (allocateListRange cx area entries.length >>= checkedTail) := by
    simp only [checkEntered, liveObjects, preflightBranch, prepared, checkedTail, Prog.bind_eq, Prog.bind_assoc]
  let canonTail := fun ptr => canonicalCollectionTail destination inst entries area output ptr >>= canonNext
  let canonProgram : AddrType → Session grow sig output.Result := fun reached => do
    let shape := layout reached element
    let ptr ← allocateListRange cx shape entries.length
    CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries
      (CanonicalTree.EntryMode.forOutput reached type output) shape.size ptr
    ListLower.publish cx destination.width ptr entries.length output
  have canonRead : right.ctl = cursor.control (.op .get fun store => canonProgram (ptrTypeIn store cx) >>= canonNext) := by
    rw [CanonicalTree.field] at canonAt
    exact canonAt
  let canonEntered := { right with ctl := cursor.control (canonProgram (ptrTypeIn right.store cx) >>= canonNext) }
  have canonStep : Step profile scheduledReady scheduledDispatch right .tau canonEntered := .get canonRead
  have canonAlloc : canonEntered.ctl = cursor.control (allocateListRange cx area entries.length >>= canonTail) := by
    simp only [canonEntered, cx, area, canonProgram, width, mode, canonTail, canonicalCollectionTail, Prog.bind_eq, Prog.bind_assoc]
  have checkInstall := listRange_install
    (profile := profile) (ready := scheduledReady) (dispatch := scheduledDispatch) cx area entries.length checkedTail checkAlloc
  have canonInstall := listRange_install
    (profile := profile) (ready := scheduledReady) (dispatch := scheduledDispatch) cx area entries.length canonTail canonAlloc
  refine ⟨chain checkSteps (.cons checkInstall (.refl _)),
    .cons canonStep (.cons canonInstall (.refl _)), ?_⟩
  dsimp only [collectionEntry, HostFrame.Paired]
  conv => rhs; rw [← same]
  exact ReturnFrame.installed (HostFrame.replace left right.host) cursor.thread _ cursor.frames cursor.rest

theorem checkPlacement {placementDispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId)
    (start : Config (core3 grow) Host) (area : Layout) (ptr : Nat) (cursor : Cursor (E := core3 grow) Host)
    (finish : P (core3 grow) Host (Ret (core3 grow)))
    (focused : start.ctl = cursor.control (do
      checkAligned ptr area.alignment.bytes
      checkInBounds (destination.context inst) ptr area.size
      finish)) :
    match placement destination start.store area ptr with
    | .ok () => Machine.Steps profile ready placementDispatch start [.tau] { start with ctl := cursor.control finish }
    | .error reason => ∃ count, Machine.Steps profile ready placementDispatch start
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg start) := by
  by_cases aligned : ptr % area.alignment.bytes = 0
  · let sizeCheck := fun (store : CStore (core3 grow)) =>
      (orTrap (.internal "dangling memory address") ((core3 grow).memSize? store.core destination.memory) >>=
        fun size => trapIf (decide (ptr + area.size > size)) .outOfBounds) >>= fun _ => finish
    have getAt : start.ctl = cursor.control (.op .get sizeCheck) := by
      have boundsAt : start.ctl = cursor.control (checkInBounds (destination.context inst) ptr area.size >>= fun _ => finish) := by
        simpa [checkAligned, trapIf, aligned] using focused
      exact boundsAt
    let read := Step.get (prof := profile) (hr := ready) (dispatch := placementDispatch) getAt
    cases sized : (core3 grow).memSize? start.store.core destination.memory with
    | none =>
      have trapAt : sizeCheck start.store = trap (.internal "dangling memory address") := by
        simp [sizeCheck, sized, orTrap, trap, Prog.bind_eq, Prog.bind]
        congr 1
        funext answer
        exact nomatch answer
      simp [placement, aligned, sized]
      exact ⟨1, .cons read (.cons (.trap (congrArg cursor.control trapAt)) (.refl _))⟩
    | some size =>
      by_cases fits : ptr + area.size ≤ size
      · have done : sizeCheck start.store = finish := by
          simp [sizeCheck, sized, orTrap, trapIf, Nat.not_lt.mpr fits]
        simp [placement, aligned, sized, Nat.not_lt.mpr fits]
        exact .cons (by simpa only [done, Cursor.control] using read) (.refl _)
      · have trapAt : sizeCheck start.store = trap .outOfBounds := by
          simp [sizeCheck, sized, orTrap, trapIf, Nat.lt_of_not_ge fits, trap, Prog.bind_eq, Prog.bind]
          congr 1
          funext answer
          exact nomatch answer
        simp [placement, aligned, sized, Nat.lt_of_not_ge fits]
        exact ⟨1, .cons read (.cons (.trap (congrArg cursor.control trapAt)) (.refl _))⟩
  · simp [checkAligned, trapIf, aligned, trap, Prog.bind_eq, Prog.bind] at focused
    simp [placement, aligned]
    exact ⟨0, .cons (.trap focused) (.refl _)⟩

theorem listEntryPlacement {entryDispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId) (element : TypeOf)
    {before after : Config (core3 grow) Host} {labels} {base count index bytes : Nat}
    (run : CoreGrowthSteps profile ready entryDispatch before labels after)
    (checked : destination.check before.store = .ok ())
    (sized : (core3 grow).memSize? before.store.core destination.memory = some bytes)
    (aligned : base = alignTo base (layout destination.width element).alignment)
    (bounds : base + count * (layout destination.width element).size ≤ bytes) (entry : index < count) :
    let area := layout destination.width element
    ptrTypeIn after.store (destination.context inst) = destination.width ∧
      placement destination after.store area (base + index * area.size) = .ok () := by
  let area := layout destination.width element
  obtain ⟨_, width, reachedSize, reached, _, range⟩ := run.linked_region (destination.context inst) rfl
    (destination.check_width before.store checked) sized bounds
  refine ⟨width, ?_⟩
  change placement destination after.store area (base + index * area.size) = .ok ()
  have baseDiv : area.alignment.bytes ∣ base :=
    ⟨(base + area.alignment.bytes - 1) / area.alignment.bytes, aligned.trans (Nat.mul_comm ..)⟩
  have offsetDiv : area.alignment.bytes ∣ index * area.size := ⟨index * area.units, by simp [Layout.size]; ac_rfl⟩
  have modulo := Nat.mod_eq_zero_of_dvd (Nat.dvd_add baseDiv offsetDiv)
  have within : base + index * area.size + area.size ≤ reachedSize := by
    rw [Nat.add_assoc, ← Nat.succ_mul]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right area.size (Nat.succ_le_of_lt entry)) base).trans range
  simp [placement, modulo, reached, Nat.not_lt.mpr within]
  rfl

theorem primitiveLeaf (destination : RecordDestination) (inst : InstId) (primitive : WIT.Primitive)
    (payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload (.prim primitive))
    (nonString : primitive ≠ .string) (index : Nat) (output : Lower.Output)
    (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (placed : rootPlacement destination left.store (.prim primitive) output = .ok ()) :
    CompareAt profile scheduledReady scheduledDispatch left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) index output)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) output) := by
  let cx := destination.context (grow := grow) inst
  change ptrTypeIn left.store cx = destination.width at width
  have well : ABI.ValType.WellFormedCM (.prim primitive : TypeOf) := by
    refine ⟨.prim _, rfl, rfl, rfl, ?_⟩
    cases primitive <;> simp [ABI.ValType.anySub, oversizedNode, layout, primitiveLayout, pointerLayout,
      pointerAlignment, Layout.size, Alignment.bytes]
  have plain : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.checkSchema (.prim primitive) = .ok () := by
    unfold Silmaril.Wasm.Game.HandleAccept.Wit.Stored.checkSchema
    rw [ite_eq_right (show ¬ containsBorrow (.prim primitive : TypeOf) = true from Bool.not_eq_true _ |>.mpr rfl),
      ite_eq_right (show ¬ payloadContainsOwn (.prim primitive) = true from Bool.not_eq_true _ |>.mpr rfl), ite_eq_left well]
  have schema : Lower.checkSchema (.prim primitive) = .ok () := by
    unfold Lower.checkSchema
    rw [plain]
    rfl
  have options : Lower.checkOptions cx (.prim primitive) output = .ok () := by
    cases primitive <;> first | contradiction | cases output <;> rfl
  have fit (width : AddrType) : Lower.fits Quirks.none cx.opts.encoding width (.prim primitive) payload.val = true := by
    cases primitive <;> first | contradiction | cases payload.val <;> rfl
  intro same checkCursor canonCursor thread checkNext canonNext checkAt canonAt
  rw [Record.Effects.field] at checkAt
  cases output with
  | flat =>
    rw [Lower.lower_flat_reference Limits.spec Quirks.none cx _ payload schema options fit] at checkAt
    let body := fun w => lowerFlatPrim (σ := HostState sig) Limits.spec Quirks.none cx w primitive payload.val
    let checkedBody : Session grow sig (Except RecordLower.Issue (List FlatValue)) := do
      return .ok (← body destination.width)
    have focus : left.ctl = checkCursor.control (.op .get (fun store =>
        (do return (Except.ok (← body (ptrTypeIn store cx)) : Except RecordLower.Issue _)) >>= checkNext)) := by
      change left.ctl = checkCursor.control
        ((((ptrType cx).bind (fun current => (body current).bind (fun words =>
          .pure (Except.ok words : Except Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Issue _)))).bind (fun
          verdict => .pure (verdict.mapError (.field index ∘ .beforeAllocation ∘ .abi)))).bind checkNext) at checkAt
      simp only [Prog.bind_assoc, Prog.pure_bind', Except.mapError] at checkAt
      change left.ctl = checkCursor.control ((Prog.op (S := Eff (core3 grow) (HostState sig)) .get
        (fun store => (body (ptrTypeIn store cx)).bind fun words => .pure (.ok words))).bind checkNext) at checkAt
      exact checkAt
    let entered := { left with ctl := checkCursor.control (checkedBody >>= checkNext) }
    have read : Step profile scheduledReady scheduledDispatch left .tau entered := by
      simpa only [width, entered, checkedBody, Cursor.control] using
        (Step.get (prof := profile) (hr := scheduledReady) (dispatch := scheduledDispatch) focus)
    have compared := compareClosed (profile := profile) (ready := scheduledReady) (dispatch := scheduledDispatch)
      (closedFlatPrim (Host := HostState sig) cx destination.width primitive payload.val nonString)
      entered right same checkCursor canonCursor thread checkNext canonNext rfl canonAt
    exact prependCheck (.cons read (.refl _)) (by simp) compared
  | memory ptr =>
    rw [Lower.lower_memory_reference Limits.spec Quirks.none cx _ payload ptr schema options fit] at checkAt
    rw [CanonicalTree.field, CanonicalTree.leaf, Field.type, Field.value, Canon.store] at canonAt
    let area := layout destination.width (.prim primitive : TypeOf)
    let body := storePrim (σ := HostState sig) Limits.spec Quirks.none cx primitive payload.val ptr
    let guarded := fun current => do
      let area := layout current (.prim primitive : TypeOf)
      checkAligned ptr area.alignment.bytes
      checkInBounds cx ptr area.size
      body
    let entered := { left with ctl := checkCursor.control (do
      checkAligned ptr area.alignment.bytes
      checkInBounds cx ptr area.size
      checkNext (.ok (← body))) }
    have focus : left.ctl = checkCursor.control (.op .get (fun store => do
        let area := layout (ptrTypeIn store cx) (.prim primitive : TypeOf)
        checkAligned ptr area.alignment.bytes
        checkInBounds cx ptr area.size
        checkNext (.ok (← body)))) := by
      rw [Canon.store] at checkAt
      change left.ctl = checkCursor.control
        ((((ptrType cx).bind (fun current => (guarded current).bind (fun value =>
          .pure (Except.ok value : Except Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Issue _)))).bind (fun
          verdict => .pure (verdict.mapError (.field index ∘ .beforeAllocation ∘ .abi)))).bind checkNext) at checkAt
      simp only [Prog.bind_assoc, Prog.pure_bind', Except.mapError] at checkAt
      change left.ctl = checkCursor.control (Prog.op (S := Eff (core3 grow) (HostState sig)) .get
        (fun store => ((guarded (ptrTypeIn store cx)).bind fun value => .pure (.ok value)).bind checkNext)) at checkAt
      refine checkAt.trans (congrArg checkCursor.control ?_)
      apply congrArg (Prog.op (S := Eff (core3 grow) (HostState sig)) .get)
      funext store
      simp only [guarded, Prog.bind_eq, Prog.bind_assoc, Prog.pure_bind']
    have read : Step profile scheduledReady scheduledDispatch left .tau entered := by
      simpa only [width, entered, area, Cursor.control] using
        (Step.get (prof := profile) (hr := scheduledReady) (dispatch := scheduledDispatch) focus)
    have guard := checkPlacement (profile := profile) (ready := scheduledReady) (placementDispatch := scheduledDispatch)
      destination inst entered area ptr checkCursor (do checkNext (.ok (← body))) rfl
    change placement destination entered.store area ptr = .ok () at placed
    rw [placed] at guard
    let checkedEnd := { entered with ctl := checkCursor.control (do checkNext (.ok (← body))) }
    have compared := compareClosed (profile := profile) (ready := scheduledReady) (dispatch := scheduledDispatch)
      (closedStorePrim (Host := HostState sig) cx primitive payload.val nonString ptr)
      checkedEnd right same checkCursor canonCursor thread checkNext canonNext (by
        change checkCursor.control (body.bind fun value => checkNext (.ok value)) =
          checkCursor.control ((body.bind fun value => .pure (.ok value)).bind checkNext)
        rw [Prog.bind_assoc]
        rfl) canonAt
    exact prependCheck (.cons read guard) (by simp) compared

theorem rootPlacementSteps (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (field : Field) (output : Lower.Output) (start : Config (core3 grow) (HostState sig))
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (finish : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (focused : start.ctl = cursor.control (Record.Effects.root recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width type field output >>= finish)) :
    let child := cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width field 0 output >>= finish)
    match rootPlacement destination start.store type output with
    | .ok () => ∃ labels, visible labels = [] ∧
        Steps profile scheduledReady scheduledDispatch start labels { start with ctl := child }
    | .error reason => ∃ count, Steps profile scheduledReady scheduledDispatch start
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg start) := by
  cases output with
  | flat =>
    refine ⟨[], rfl, ?_⟩
    change start.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width field 0 .flat >>= finish) at focused
    have entered : start = { start with ctl := cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width field 0 .flat >>= finish) } := by
      conv => rhs; rw [← focused]
    exact entered ▸ .refl start
  | memory ptr =>
    let area := layout destination.width type
    let body := Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width field 0 (.memory ptr) >>= finish
    have guardAt : start.ctl = cursor.control (do
        checkAligned ptr area.alignment.bytes
        checkInBounds (destination.context inst) ptr area.size
        body) := by
      rw [focused]
      simp only [Record.Effects.root, body, area, Prog.bind_eq, Prog.bind_assoc]
    have run := checkPlacement (profile := profile) (ready := scheduledReady) (placementDispatch := scheduledDispatch)
      destination inst start area ptr cursor body guardAt
    change (match placement destination start.store area ptr with
      | .ok () => _ | .error _ => _)
    cases verdict : placement destination start.store area ptr with
    | error _ => rw [verdict] at run; exact run
    | ok result => cases result; rw [verdict] at run; exact ⟨[.tau], rfl, run⟩

theorem compiledFlat (left right : Config (core3 grow) (HostState sig)) (sameStore : left.store = right.store)
    (destination : RecordDestination) (inst : InstId) (tag : sig.Tag)
    (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat} (children : Fin arity → OwnedMemory.Tree sig)
    (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload .flat = .ok (field, plan)) (fragment : HandleShape field)
    (checked : destination.check left.store = .ok ()) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (sameThread : checkCursor.thread = canonCursor.thread)
    (checkNext : Except RecordLower.Issue (List FlatValue) → Session grow sig (Ret (core3 grow)))
    (canonNext : List FlatValue → Session grow sig (Ret (core3 grow)))
    (checkAt : left.ctl = checkCursor.control (Record.Effects.lowerTree recordClaims Limits.spec Quirks.none
      (destination.context inst) (.tag ⟨tag, payload⟩ arity children) .flat >>= checkNext))
    (canonAt : right.ctl = canonCursor.control (lowerFlatAt Limits.spec Quirks.none (destination.context inst)
      destination.width payload.val.value (sig.payload tag) >>= canonNext)) :
    Reaches profile scheduledReady scheduledDispatch left right checkCursor canonCursor checkNext canonNext := by
  have start := destination.compiled_payload_effects (profile := profile) (ready := scheduledReady)
    (dispatch := scheduledDispatch) left inst tag payload .flat field plan checkNext compiled checked checkAt
  have certified := certifyField start.2.1 fragment
  have reference := destination.compiled_payload_reference (grow := grow) (World := HostState sig)
    inst (sig.payload tag) payload .flat field plan compiled
  have canonField : right.ctl = canonCursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width field .flat >>= canonNext) := by
    rw [reference]
    exact canonAt
  have entry := start.2.2.2
  cases verdict : Record.prepare left.store left.host.writer field.objects with
  | error issue =>
    rw [verdict] at entry
    exact ⟨.refused issue, [.tau, .tau], [], _, right, entry, .refl right, sameStore, rfl, rfl⟩
  | ok passed =>
    cases passed
    rw [verdict] at entry
    cases fits : Lower.fits Quirks.none destination.encoding destination.width (sig.payload tag) payload.val.value with
    | false =>
      simp only [fits, Bool.not_false, ↓reduceIte] at entry
      exact ⟨.refused (.preflight (.abi .allocationPrecondition)), [.tau, .tau, .tau], [], _, right,
        entry, .refl right, sameStore, rfl, rfl⟩
    | true =>
      simp only [fits, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at entry
      let entered := { left with ctl := checkCursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width field 0 .flat >>= checkNext) }
      have continued := flatField (profile := profile) (scheduledReady := scheduledReady)
        (scheduledDispatch := scheduledDispatch) destination inst field certified 0 entered right sameStore
        checkCursor canonCursor sameThread checkNext canonNext rfl canonField
      exact prependCheck entry (by simp) continued

theorem parkedFlat (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (handleWord : BitVec IntType.i32.width) (destination : RecordDestination) (inst : InstId) (schema : TypeOf)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat}
    (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload .flat = .ok (field, plan)) (fragment : HandleShape field)
    (start reference : Config (core3 grow) (HostState sig)) (sameStore : start.store = reference.store)
    (canonCursor : Cursor (E := core3 grow) (HostState sig)) (canonNext : List FlatValue → Session grow sig (Ret (core3 grow)))
    {thread core continuation segments rest} (sameThread : thread = canonCursor.thread)
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handleWord])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .giveFlat destination schema⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Endpoints.Core.childFromHistory start.host.writer.accepted handleWord =
      some (.tag ⟨tag, payload⟩ arity children))
    (schemaChecked : rootHasSchema (.tag ⟨tag, payload⟩ arity children) schema = true)
    (canonicalAt : reference.ctl = canonCursor.control (lowerFlatAt Limits.spec Quirks.none (destination.context inst)
      destination.width payload.val.value (sig.payload tag) >>= canonNext)) :
    Reaches profile scheduledReady (specDispatch scheduledReady (host (grow := grow) bindings)) start reference
      ⟨thread, .core core continuation :: segments, rest⟩ canonCursor
      (flatReply destination schema start.host.nextTicket) canonNext := by
  let route := GiveEffectRoute.flat schema
  let tree : OwnedMemory.Tree sig := .tag ⟨tag, payload⟩ arity children
  let entered := { start with
    host := start.host.enter name type (route.args handleWord)
    ctl := ⟨thread, .prog (route.run destination inst tree start.host.nextTicket),
      .core core continuation :: segments⟩ :: rest }
  obtain ⟨labels, allTau, run⟩ := route.parked bindings name type handleWord inst destination tree
    start thread profile scheduledReady parked calling linked caller mayLeave destinationChecked selected schemaChecked
  have continued := compiledFlat (profile := profile) (scheduledReady := scheduledReady)
    (scheduledDispatch := specDispatch scheduledReady (host bindings)) entered reference sameStore
    destination inst tag payload children field plan compiled fragment destinationChecked
    ⟨thread, .core core continuation :: segments, rest⟩ canonCursor sameThread
    (flatReply destination schema start.host.nextTicket) canonNext rfl canonicalAt
  exact prependCheck run (fun label member => by
    have test := List.all_eq_true.mp allTau label member
    cases label <;> simp_all) continued

private theorem compiledMemory (left right : Config (core3 grow) (HostState sig)) (sameStore : left.store = right.store)
    (destination : RecordDestination) (inst : InstId) (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag))
    {arity : Nat} (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object) (ptr : Nat)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload (.memory ptr) = .ok (field, plan)) (fragment : MemoryHandleRoot field)
    (destinationChecked : destination.check left.store = .ok ())
    (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig)) (sameThread : checkCursor.thread = canonCursor.thread)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (checkAt : left.ctl = checkCursor.control (Record.Effects.lowerTree recordClaims Limits.spec Quirks.none
      (destination.context inst) (.tag ⟨tag, payload⟩ arity children) (.memory ptr) >>= checkNext))
    (canonAt : right.ctl = canonCursor.control (store Limits.spec Quirks.none (destination.context inst)
      payload.val.value (sig.payload tag) ptr >>= canonNext)) :
    MemoryReaches profile scheduledReady scheduledDispatch left right checkCursor canonCursor checkNext canonNext
      (placement destination left.store (layout destination.width (sig.payload tag)) ptr) := by
  have started := destination.compiled_payload_effects (profile := profile) (ready := scheduledReady)
    (dispatch := scheduledDispatch) (reached := left) inst tag payload (.memory ptr) field plan checkNext
    compiled destinationChecked checkAt
  have reference := destination.compiled_payload_reference (grow := grow) (World := HostState sig)
    inst (sig.payload tag) payload (.memory ptr) field plan compiled
  have canonField : right.ctl = canonCursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width field (.memory ptr) >>= canonNext) := by
    rw [reference]
    exact canonAt
  have entry := started.2.2.2
  cases verdict : Record.prepare left.store left.host.writer field.objects with
  | error issue =>
    rw [verdict] at entry
    exact .inl ⟨.refused issue, [.tau, .tau], [], _, right, entry, .refl right, sameStore, rfl, rfl⟩
  | ok passed =>
    cases passed
    rw [verdict] at entry
    cases fits : Lower.fits Quirks.none destination.encoding destination.width (sig.payload tag) payload.val.value with
    | false =>
      simp only [fits, Bool.not_false, ↓reduceIte] at entry
      exact .inl ⟨.refused (.preflight (.abi .allocationPrecondition)), [.tau, .tau, .tau], [], _, right,
        entry, .refl right, sameStore, rfl, rfl⟩
    | true =>
      simp only [fits, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at entry
      let area := layout destination.width (sig.payload tag)
      let emit : Session grow sig (Except RecordLower.Issue Unit) :=
        Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width field 0 (.memory ptr)
      let body := emit >>= checkNext
      let guarded := { left with ctl := checkCursor.control (Record.Effects.root recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width (sig.payload tag) field (.memory ptr) >>= checkNext) }
      have entered : Machine.Steps profile scheduledReady scheduledDispatch left [.tau, .tau, .tau] guarded := entry
      have guardAt : guarded.ctl = checkCursor.control (do
        checkAligned ptr area.alignment.bytes
        checkInBounds (destination.context inst) ptr area.size
        body) := by
        change checkCursor.control (((checkAligned ptr area.alignment.bytes).bind fun _ =>
          (checkInBounds (destination.context inst) ptr area.size).bind fun _ => emit).bind checkNext) = _
        simp only [body, Prog.bind_eq, Prog.bind_assoc]
      have checked := checkPlacement (profile := profile) (ready := scheduledReady) (placementDispatch := scheduledDispatch)
        destination inst guarded area ptr checkCursor body guardAt
      change (match placement destination left.store area ptr with
        | .ok () => _ | .error reason => _) at checked
      cases result : placement destination left.store area ptr with
      | ok valid =>
        cases valid
        rw [result] at checked
        have width : ptrTypeIn right.store (destination.context inst) = destination.width := by
          rw [← sameStore]
          simp [ptrTypeIn, RecordDestination.context, CanonOpts.ptrType,
            destination.check_width left.store destinationChecked]
        let placed := { left with ctl := checkCursor.control body }
        have continued := memoryHandleRoot (profile := profile) (scheduledReady := scheduledReady)
          (scheduledDispatch := scheduledDispatch) destination inst field 0 ptr placed right width fragment sameStore
          checkCursor canonCursor sameThread checkNext canonNext rfl canonField
        exact .inl (prependCheck (chain entered checked) (by simp) continued)
      | error reason =>
        rw [result] at checked
        obtain ⟨count, halted⟩ := checked
        refine .inr ⟨reason, 3 + count, StepDefs.trapCfg guarded, rfl, ?_, rfl, rfl⟩
        rw [List.replicate_add, List.append_assoc]
        exact chain entered halted

theorem parkedMemory (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (handleWord : BitVec IntType.i32.width) (pointer : FlatValue) (destination : RecordDestination) (inst : InstId)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat}
    (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload (.memory (flatNat pointer)) = .ok (field, plan)) (fragment : MemoryHandleRoot field)
    (start reference : Config (core3 grow) (HostState sig)) (sameStore : start.store = reference.store)
    (canonCursor : Cursor (E := core3 grow) (HostState sig)) (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {thread core continuation segments rest} (sameThread : thread = canonCursor.thread)
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handleWord, pointer])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .givePayload destination⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Endpoints.Core.childFromHistory start.host.writer.accepted handleWord =
      some (.tag ⟨tag, payload⟩ arity children))
    (pointerChecked : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.flatType pointer = pointerType destination.width)
    (canonicalAt : reference.ctl = canonCursor.control (store Limits.spec Quirks.none (destination.context inst)
      payload.val.value (sig.payload tag) (flatNat pointer) >>= canonNext)) :
    MemoryReaches profile scheduledReady (specDispatch scheduledReady (host (grow := grow) bindings)) start reference
      ⟨thread, .core core continuation :: segments, rest⟩ canonCursor
      (memoryReply destination pointer start.host.nextTicket) canonNext
      (placement destination start.store (layout destination.width (sig.payload tag)) (flatNat pointer)) := by
  let route := GiveEffectRoute.memory pointer
  let tree : OwnedMemory.Tree sig := .tag ⟨tag, payload⟩ arity children
  let entered := { start with
    host := start.host.enter name type (route.args handleWord)
    ctl := ⟨thread, .prog (route.run destination inst tree start.host.nextTicket),
      .core core continuation :: segments⟩ :: rest }
  obtain ⟨labels, allTau, run⟩ := route.parked bindings name type handleWord inst destination tree
    start thread profile scheduledReady parked calling linked caller mayLeave destinationChecked selected pointerChecked
  have continued := compiledMemory (profile := profile) (scheduledReady := scheduledReady)
    (scheduledDispatch := specDispatch scheduledReady (host bindings)) entered reference sameStore
    destination inst tag payload children field plan (flatNat pointer) compiled fragment destinationChecked
    ⟨thread, .core core continuation :: segments, rest⟩ canonCursor sameThread
    (memoryReply destination pointer start.host.nextTicket) canonNext rfl canonicalAt
  have noEvents : ∀ label ∈ labels, label = (.tau : Label (core3 grow) (HostState sig)) := by
    intro label member
    have test := List.all_eq_true.mp allTau label member
    cases label <;> simp_all
  rcases continued with paired | ⟨reason, count, reached, refused, halted, empty, stores⟩
  · exact .inl (prependCheck run noEvents paired)
  · have replicated : labels = List.replicate labels.length (.tau : Label (core3 grow) (HostState sig)) :=
      List.eq_replicate_length.mpr noEvents
    refine .inr ⟨reason, labels.length + count, reached, refused, ?_, empty, stores⟩
    rw [List.replicate_add, ← replicated, List.append_assoc]
    exact chain run halted

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix

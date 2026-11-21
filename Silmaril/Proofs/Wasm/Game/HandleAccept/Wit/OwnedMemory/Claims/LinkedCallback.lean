module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCollection.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}
  {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}

private theorem silent (count : Nat) :
    PayloadPrefix.visible (List.replicate count .tau : List (Label (core3 grow) (HostState sig))) = [] := by
  induction count with
  | zero => rfl
  | succ _ ih => simpa only [List.replicate_succ, PayloadPrefix.visible, List.filter_cons, Bool.false_eq_true, ↓reduceIte] using ih

theorem replayFor {left right last : State grow sig} {visibleLabels}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    (path : PrefixFor profile ready bindings protectedReturn left visibleLabels last)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes left right) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    ∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels last ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Related.Paired changes last other ∧
      PayloadPrefix.visible leftLabels = visibleLabels ∧ PayloadPrefix.visible rightLabels = visibleLabels := by
  induction path generalizing right with
  | done cfg => exact ⟨[], [], right, .refl _, .refl _, paired, rfl, rfl⟩
  | step inside growth run _ ih =>
    obtain ⟨_, replay, matched⟩ := HostFrame.Related.interior_step covers paired inside growth run
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
  | @syncReady start _ _ task inst thread frames rest focused agrees _ ih =>
    let chooseNext := syncLiftCandidates (E := core3 grow) (σ := HostState sig) task
    let residual := chooseNext (start.store.instCandidates (ready start.host) inst)
    obtain ⟨otherFrames, otherRest, atOther, matched⟩ := paired.retarget focused (.prog residual) start.host right.host
    have candidates := HostFrame.instCandidates_eq start.store inst (ready start.host) (ready right.host)
      (fun entry live thread member suspended found blocked query condition =>
        agrees entry live thread member suspended found blocked query condition right.host)
    have stepRight : Machine.Step profile ready (specDispatch ready (host (grow := grow) bindings)) right .tau
        { right with ctl := ⟨thread, .prog residual, otherFrames⟩ :: otherRest } := by
      change Machine.Step _ _ _ _ _ { right with ctl := ⟨thread,
        .prog (chooseNext (start.store.instCandidates (ready start.host) inst)), otherFrames⟩ :: otherRest }
      rw [candidates]
      exact .hostGet atOther
    obtain ⟨leftLabels, rightLabels, other, lhs, rhs, still, seenLeft, seenRight⟩ := ih matched
    exact ⟨.tau :: leftLabels, .tau :: rightLabels, other,
      .cons (by simp [CoreUpdateGrows, focused]) (.hostGet focused) lhs,
      .cons (by simp [CoreUpdateGrows, atOther]) stepRight rhs, still, seenLeft, seenRight⟩

theorem replay {left right last : State grow sig} {visibleLabels}
    (path : Prefix profile ready bindings first left visibleLabels last)
    (paired : HostFrame.Paired first second left right) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    ∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels last ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second last other ∧
      PayloadPrefix.visible leftLabels = visibleLabels ∧ PayloadPrefix.visible rightLabels = visibleLabels :=
  replayFor path (fun _ _ edge => by cases edge; rfl) paired

theorem syncLift {start last : State grow sig} {labels task thread frames rest} {entry : Task (core3 grow)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    (focused : start.ctl = ⟨thread, .prog (syncLiftLoopBody ready task), frames⟩ :: rest)
    (found : ArenaField.tasks.get? start.store task = some entry) (waiting : entry.state ≠ .resolved)
    (agrees : ReadyAgreement ready start entry.inst)
    (path : PrefixFor profile ready bindings protectedReturn { start with ctl := ⟨thread,
      .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) entry.inst)), frames⟩ :: rest }
      labels last) : PrefixFor profile ready bindings protectedReturn start labels last := by
  let read : CStore (core3 grow) → Session grow sig (Ret (core3 grow)) := fun store =>
    .op .hostGet fun current => syncLiftCandidates task (store.instCandidates (ready current) entry.inst)
  let begin : CStore (core3 grow) → Session grow sig (Ret (core3 grow)) := fun store =>
    ((match ArenaField.tasks.get? store task with
      | some info => pure info
      | none => internal "dangling arena id") : Session grow sig (Task (core3 grow))) >>= fun info =>
    if info.state = .resolved then pure .unit else .op .get fun reached =>
      .op .hostGet fun current => syncLiftCandidates task (reached.instCandidates (ready current) info.inst)
  have body : syncLiftLoopBody ready task = .op .get begin := by
    change Prog.op (S := Eff (core3 grow) (HostState sig)) .get _ = Prog.op (S := Eff (core3 grow) (HostState sig)) .get _
    congr 1
    funext store
    dsimp only [begin, Prog.bind]
    cases ArenaField.tasks.get? store task
    · rfl
    · simp only [Prog.bind_eq, Prog.pure_eq, Prog.pure_bind']
      split <;> rfl
  have atStart : start.ctl = ⟨thread, .prog (.op .get begin), frames⟩ :: rest := body ▸ focused
  have firstRead : begin start.store = .op .get read := by
    simp only [begin, found, pure_bind, ite_eq_right waiting]
    rfl
  have stepFirst := Machine.Step.get (prof := profile) (hr := ready)
    (dispatch := specDispatch ready (host (grow := grow) bindings)) atStart
  rw [firstRead] at stepFirst
  refine .step ?_ (by simp [CoreUpdateGrows, atStart]) stepFirst
    (.step ?_ (by trivial) (.get rfl) (.syncReady rfl agrees path))
  · rw [HostFrame.InteriorFor, atStart]
    refine ⟨?_, ?_⟩
    · intro _ _ _ _ impossible
      cases impossible
    · intro _ _ _ _ _ _ impossible
      cases impossible
  · unfold HostFrame.InteriorFor
    refine ⟨?_, ?_⟩
    · intro _ _ _ _ impossible
      cases impossible
    · intro _ _ _ _ _ _ impossible
      cases impossible

private theorem classifyPopFor {left right : State grow sig} {thread value frames rest}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (commonHost : HostState sig) (paired : ReturnFrame.Related.Paired changes (HostFrame.replace left commonHost) right)
    (focused : left.ctl = ⟨thread, .prog (.pure value), .prog resume :: frames⟩ :: rest) :
    ∃ otherFrames otherRest,
      (∃ otherResume, changes resume otherResume ∧
        right.ctl = ⟨thread, .prog (.pure value), .prog otherResume :: otherFrames⟩ :: otherRest ∧
        ChildFrameOver changes left right ⟨thread, frames, rest⟩ ⟨thread, otherFrames, otherRest⟩) ∨
      (right.ctl = ⟨thread, .prog (.pure value), .prog resume :: otherFrames⟩ :: otherRest ∧
       HostFrame.Related.Paired changes { left with ctl := ⟨thread, .prog (resume value), frames⟩ :: rest }
         { right with ctl := ⟨thread, .prog (resume value), otherFrames⟩ :: otherRest }) := by
  cases paired with
  | mk control blocked =>
    change List.Forall₂ _ left.ctl _ at control
    rw [focused] at control
    cases control with
    | cons active tail =>
      cases active with
      | mk segments =>
        cases segments with
        | cons top below =>
          cases top with
          | swap edge => exact ⟨_, _, .inl ⟨_, edge, rfl, ⟨rfl, rfl, rfl, rfl, blocked, rfl, below, tail⟩⟩⟩
          | same => exact ⟨_, _, .inr ⟨rfl, .mk (.cons (.mk below) tail) blocked⟩⟩

private theorem classifyPop {left right : State grow sig} {thread value frames rest}
    (commonHost : HostState sig) (paired : ReturnFrame.Paired first second (HostFrame.replace left commonHost) right)
    (focused : left.ctl = ⟨thread, .prog (.pure value), .prog first :: frames⟩ :: rest) :
    ∃ otherFrames otherRest,
      (right.ctl = ⟨thread, .prog (.pure value), .prog second :: otherFrames⟩ :: otherRest ∧
        ChildFrame first second left right ⟨thread, frames, rest⟩ ⟨thread, otherFrames, otherRest⟩) ∨
      (right.ctl = ⟨thread, .prog (.pure value), .prog first :: otherFrames⟩ :: otherRest ∧
       HostFrame.Paired first second { left with ctl := ⟨thread, .prog (first value), frames⟩ :: rest }
         { right with ctl := ⟨thread, .prog (first value), otherFrames⟩ :: otherRest }) := by
  obtain ⟨otherFrames, otherRest, ⟨_, edge, atOther, frame⟩ | common⟩ := classifyPopFor commonHost paired focused
  · cases edge
    exact ⟨otherFrames, otherRest, .inl ⟨atOther, frame⟩⟩
  · exact ⟨otherFrames, otherRest, .inr common⟩

theorem returnCutFor {left right last : State grow sig} {seen value}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    {resume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (path : PrefixFor profile ready bindings protectedReturn left seen last)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes left right) (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog resume :: cursor.frames }.control (pure value)) :
    CallbackReturnFor profile ready bindings changes left right last cursor resume value seen := by
  obtain ⟨leftLabels, rightLabels, other, lhs, rhs, reached, seenLeft, seenRight⟩ := replayFor path covers paired
  have checked := lhs.append (.cons (by simp [CoreUpdateGrows, leftAt, Cursor.control]) (.popProg leftAt) (.refl _))
  have invisible (labels : List (Label (core3 grow) (HostState sig))) : visible (labels ++ [.tau]) = visible labels :=
    (List.filter_append labels [.tau]).trans (List.append_nil _)
  obtain ⟨otherFrames, otherRest, ⟨_, edge, atPop, frame⟩ | ⟨atCommon, still⟩⟩ :=
    classifyPopFor other.host reached leftAt
  · have canonical := rhs.append (.cons (by simp [CoreUpdateGrows, atPop]) (.popProg atPop) (.refl _))
    exact .substituted edge frame checked canonical ((invisible _).trans seenLeft) ((invisible _).trans seenRight)
  · have canonical := rhs.append (.cons (by simp [CoreUpdateGrows, atCommon]) (.popProg atCommon) (.refl _))
    exact .common checked canonical still ((invisible _).trans seenLeft) ((invisible _).trans seenRight)

theorem returnCut {left right last : State grow sig} {seen value}
    (path : Prefix profile ready bindings first left seen last) (paired : HostFrame.Paired first second left right)
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure value)) :
    CallbackReturn profile ready bindings first second left right last cursor value seen := by
  cases returnCutFor path (fun _ _ edge => by cases edge; rfl) paired cursor leftAt with
  | substituted edge frame checked canonical seenLeft seenRight =>
    cases edge
    exact .designated frame checked canonical seenLeft seenRight
  | common checked canonical still seenLeft seenRight => exact .common checked canonical still seenLeft seenRight

theorem stringReallocPair (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (checkAt : left.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : right.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let leftEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext left cursor
    let rightEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps canonNext right cursor
    Step profile ready dispatch left .tau leftEntry ∧ Step profile ready dispatch right .tau rightEntry ∧
    HostFrame.Paired (stringPlanResume cx steps checkNext) (stringPlanResume cx steps canonNext) leftEntry rightEntry := by
  refine ⟨string_realloc_install cx ptr oldSize alignment size steps checkNext left cursor checkAt,
    string_realloc_install cx ptr oldSize alignment size steps canonNext right cursor canonAt, ?_⟩
  dsimp only [stringReallocEntry, HostFrame.Paired]
  conv => rhs; rw [← same]
  exact ReturnFrame.installed (HostFrame.replace left right.host) cursor.thread _ cursor.frames cursor.rest

private theorem childFrameEnter {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (body : Session grow sig (Ret (core3 grow)))
    (first second : ReturnFrame.Continuation (core3 grow) (HostState sig)) :
    HostFrame.Related.Paired (ReturnFrame.Extend changes first second)
      { left with ctl := { check with frames := .prog first :: check.frames }.control body }
      { right with ctl := { canon with frames := .prog second :: canon.frames }.control body } := by
  have data : { HostFrame.replace left right.host with ctl := canon.control body, conts := right.conts } =
      { right with ctl := canon.control body } := by
    have store := frame.store
    have pending := frame.pending
    have results := frame.results
    have cancels := frame.cancels
    cases left; cases right; simp_all [HostFrame.replace]
  have paired : ReturnFrame.Related.Paired changes
      { HostFrame.replace left right.host with ctl := check.control body } { right with ctl := canon.control body } := by
    rw [← data]
    have head : ReturnFrame.Related.Active changes ⟨check.thread, .prog body, check.frames⟩
        ⟨canon.thread, .prog body, canon.frames⟩ := by
      rw [← frame.thread]
      exact .mk frame.frames
    exact .mk (.cons head frame.rest) frame.blocked
  obtain ⟨otherFrames, otherRest, otherAt, installed⟩ := ReturnFrame.Related.Paired.push paired
    (thread := check.thread) (focus := .prog body) (frames := check.frames) (rest := check.rest) rfl body first second
  change canon.control body = ⟨check.thread, .prog body, otherFrames⟩ :: otherRest at otherAt
  have tails : canon.frames = otherFrames ∧ canon.rest = otherRest := by
    simpa [Cursor.control, frame.thread] using otherAt
  simpa only [Cursor.control, HostFrame.Related.Paired, HostFrame.replace, ← tails.1, ← tails.2, frame.thread]
    using installed

theorem childStringRealloc {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (checkAt : left.ctl = check.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let leftEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext left check
    let rightEntry := stringReallocEntry ready bindings cx ptr oldSize alignment size steps canonNext right canon
    Step profile ready dispatch left .tau leftEntry ∧ Step profile ready dispatch right .tau rightEntry ∧
    HostFrame.Related.Paired (ReturnFrame.Extend changes (stringPlanResume cx steps checkNext)
      (stringPlanResume cx steps canonNext)) leftEntry rightEntry :=
  ⟨string_realloc_install cx ptr oldSize alignment size steps checkNext left check checkAt,
    string_realloc_install cx ptr oldSize alignment size steps canonNext right canon canonAt,
    childFrameEnter frame _ _ _⟩

theorem childCollectionInstall {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver changes left right check canon)
    (reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host bindings)
    let area := layout destination.width element
    let first := checkedCollectionResume destination inst entries area index output checkNext
    let second := canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkCall := collectionEntry destination inst area entries.length dispatch left check first
    let canonCall := collectionEntry destination inst area entries.length dispatch right canon second
    Steps profile ready dispatch left [.tau, .tau, .tau] checkCall ∧
    Steps profile ready dispatch right [.tau, .tau] canonCall ∧
    HostFrame.Related.Paired (ReturnFrame.Extend changes first second) checkCall canonCall := by
  obtain ⟨checked, canonical⟩ := collection_install_steps (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (host (grow := grow) bindings)) destination inst type element entries output index
    left right check canon checkNext canonNext reachedWidth prepared checkAt canonAt
  exact ⟨checked, canonical, childFrameEnter frame _ _ _⟩

theorem rangeCutOver (destination : RecordDestination) (inst : InstId) (area : Layout) (count pointer : Nat) (plan : List Object)
    {left right last : State grow sig} {seen}
    {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {protectedReturn : ReturnFrame.Continuation (core3 grow) (HostState sig) → Prop}
    (path : PrefixFor profile ready bindings protectedReturn left seen last)
    (covers : ∀ first second, changes first second → protectedReturn first)
    (paired : HostFrame.Related.Paired changes left right) (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Nat → Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area count pointer
      let live ← Record.Effects.reserve recordClaims plan
      checkNext ptr live))
    (canonBody : ∀ resume, changes first resume →
      resume (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= canonNext)) :
    RangeCutOver profile ready bindings changes first left right last cursor destination area count pointer plan checkNext canonNext seen := by
  obtain ⟨leftLabels, rightLabels, other, lhs, rhs, reached, seenLeft, seenRight⟩ := replayFor path covers paired
  obtain ⟨otherFrames, otherRest, ⟨resume, edge, atPop, frame⟩ | ⟨atCommon, still⟩⟩ := classifyPopFor other.host reached leftAt
  · let canonCursor : Cursor (E := core3 grow) (HostState sig) := ⟨cursor.thread, otherFrames, otherRest⟩
    have width := lhs.grows.memAddrType present
    obtain ⟨reachedBytes, reachedSize, _⟩ := lhs.grows.memSize sized
    have validation := destination.paired_range_recheck (profile := profile) (ready := ready)
      (dispatch := specDispatch ready (host (grow := grow) bindings)) reached inst area count pointer plan
      checkNext canonNext checkBody (canonBody resume edge) leftAt atPop reachedSize
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    have append {start middle finish : State grow sig} {leading trailing : List (Label (core3 grow) (HostState sig))}
        (run : Steps profile ready dispatch start leading middle)
        (next : Steps profile ready dispatch middle trailing finish) :
        Steps profile ready dispatch start (leading ++ trailing) finish := by
      induction run with
      | refl => exact next
      | cons step _ ih => exact .cons step (ih next)
    have trapped (reason : TrapReason)
        (checked : ∃ steps, Steps profile ready dispatch last (List.replicate steps .tau ++ [.trap reason])
          (StepDefs.trapCfg last))
        (canonical : ∃ steps, Steps profile ready dispatch other (List.replicate steps .tau ++ [.trap reason])
          (StepDefs.trapCfg other)) :
        RangeCutOver profile ready bindings changes first left right last cursor destination area count pointer plan checkNext canonNext seen := by
      obtain ⟨checkCount, checked⟩ := checked
      obtain ⟨canonCount, canonical⟩ := canonical
      refine .trapped (reason := reason) frame.store (append lhs.steps checked) (append rhs.steps canonical) ?_ ?_
      · rw [show visible (leftLabels ++ (List.replicate checkCount .tau ++ [.trap reason])) =
          visible leftLabels ++ (visible (List.replicate checkCount .tau) ++ visible [.trap reason]) from by
          simp only [visible, List.filter_append], seenLeft, silent checkCount]; rfl
      · rw [show visible (rightLabels ++ (List.replicate canonCount .tau ++ [.trap reason])) =
          visible rightLabels ++ (visible (List.replicate canonCount .tau) ++ visible [.trap reason]) from by
          simp only [visible, List.filter_append], seenRight, silent canonCount]; rfl
    dsimp only at validation
    by_cases unaligned : pointer ≠ alignTo pointer area.alignment
    · rw [ite_eq_left unaligned] at validation
      exact trapped .unalignedPointer validation.1 validation.2
    by_cases fits : pointer + count * area.size ≤ reachedBytes
    · rw [ite_eq_right unaligned, ite_eq_left fits] at validation
      obtain ⟨⟨checkLabels, checkSilent, checkSteps⟩, ⟨canonLabels, canonSilent, canonSteps⟩⟩ := validation
      have hide {labels : List (Label (core3 grow) (HostState sig))}
          (allTau : ∀ label ∈ labels, label = .tau) : visible labels = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro label member
        simp only [allTau label member, Bool.false_eq_true, not_false_eq_true]
      refine .reached (canonCursor := canonCursor) width reachedSize (Classical.not_not.mp unaligned) fits frame lhs.grows
        (append lhs.steps checkSteps) (append rhs.steps canonSteps) ?_ ?_
      · rw [show visible (leftLabels ++ checkLabels) = visible leftLabels ++ visible checkLabels from List.filter_append ..,
          seenLeft, hide checkSilent, List.append_nil]
      · rw [show visible (rightLabels ++ canonLabels) = visible rightLabels ++ visible canonLabels from List.filter_append ..,
          seenRight, hide canonSilent, List.append_nil]
    · rw [ite_eq_right unaligned, ite_eq_right fits] at validation
      exact trapped .outOfBounds validation.1 validation.2
  · refine .common ⟨leftLabels ++ [.tau], rightLabels ++ [.tau], _,
      (lhs.append (.cons ?_ (.popProg leftAt) (.refl _))).steps,
      (rhs.append (.cons ?_ (.popProg atCommon) (.refl _))).steps, still, ?_, ?_⟩
    · simp [CoreUpdateGrows, leftAt, Cursor.control]
    · simp [CoreUpdateGrows, atCommon]
    · simpa only [visible, List.filter_append, List.filter_cons, List.filter_nil, Bool.false_eq_true,
        ↓reduceIte, List.append_nil] using seenLeft
    · simpa only [visible, List.filter_append, List.filter_cons, List.filter_nil, Bool.false_eq_true,
        ↓reduceIte, List.append_nil] using seenRight

theorem rangeCut (destination : RecordDestination) (inst : InstId) (area : Layout) (count pointer : Nat) (plan : List Object)
    {left right last : State grow sig} {seen} (path : Prefix profile ready bindings first left seen last)
    (paired : HostFrame.Paired first second left right) (cursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { cursor with frames := .prog first :: cursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Nat → Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area count pointer
      let live ← Record.Effects.reserve recordClaims plan
      checkNext ptr live))
    (canonBody : second (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= canonNext)) :
    RangeCut profile ready bindings first second left right last cursor destination area count pointer plan checkNext canonNext seen :=
  rangeCutOver destination inst area count pointer plan path (fun _ _ edge => by cases edge; rfl)
    paired cursor leftAt present sized checkNext canonNext checkBody (fun _ edge => by cases edge; exact canonBody)

theorem collectionDescent (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index : Nat) (left right : State grow sig) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (present : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? right.store.core destination.memory = some bytes)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    CollectionDescent profile ready bindings destination inst type element entries output index left right cursor checkNext canonNext := by
  dsimp only [CollectionDescent]
  obtain ⟨checked, canonical, paired⟩ := PayloadPrefix.collection_install_mode (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (host (grow := grow) bindings)) destination inst type element entries output index
    left right cursor checkNext canonNext same present prepared checkAt canonAt
  have stores : left.store = right.store := by simpa only using congrArg (fun cfg : State grow sig => cfg.store) same
  refine ⟨checked, canonical, paired, ?_⟩
  intro last seen path reached pointer atReturn
  exact rangeCut destination inst (layout destination.width element) entries.length pointer (Field.listObjects entries)
    path paired reached atReturn (stores ▸ present) (stores ▸ sized) _ _ rfl rfl

private theorem collectionReturnKeeping (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    {left right last : State grow sig} {labels} (path : Prefix profile ready bindings first left labels last)
    (paired : HostFrame.Paired first second left right) (checkCursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { checkCursor with frames := .prog first :: checkCursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : second (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    {keep : CStore (core3 grow) → Prop}
    (compared : Core3.Grows left.store.core last.store.core → ∀ reference reachedBytes,
      ptrTypeIn last.store (destination.context inst) = destination.width →
      (core3 grow).memSize? last.store.core destination.memory = some reachedBytes →
      CollectionTailKeepingAt profile ready (specDispatch ready (host bindings)) keep destination inst entries area
        output index pointer reachedBytes last reference) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    (∃ canonCursor, canonCursor.thread = checkCursor.thread ∧
      ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext) ∨
    (∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels { last with ctl := checkCursor.control (first (.nat pointer)) } ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second { last with ctl := checkCursor.control (first (.nat pointer)) } other ∧
      visible leftLabels = labels ∧ visible rightLabels = labels) := by
  obtain ⟨leftLabels, rightLabels, other, lhs, rhs, reached, seenLeft, seenRight⟩ := replay path paired
  obtain ⟨otherFrames, otherRest, ⟨atPop, _⟩ | ⟨atCommon, still⟩⟩ := classifyPop other.host reached leftAt
  · let canonCursor : Cursor (E := core3 grow) (HostState sig) := ⟨checkCursor.thread, otherFrames, otherRest⟩
    have region := lhs.linked_region (destination.context inst) (start := 0) (length := 0)
      rfl present sized (by simp)
    obtain ⟨_, reachedWidth, bytes, reachedSize, _, _⟩ := region
    have continued := PayloadPrefix.collection_return_keeping_at destination inst entries area output index pointer last other
      checkCursor canonCursor checkNext canonNext first second reached rfl leftAt atPop checkBody canonBody reachedSize
      (compared lhs.grows other bytes reachedWidth reachedSize)
    exact .inl ⟨canonCursor, rfl, continued.prepend lhs.steps rhs.steps (seenLeft.trans seenRight.symm)⟩
  · refine .inr ⟨leftLabels ++ [.tau], rightLabels ++ [.tau], _, lhs.append (.cons ?_ (.popProg leftAt) (.refl _)),
      rhs.append (.cons ?_ (.popProg atCommon) (.refl _)), still, ?_, ?_⟩
    · simp [CoreUpdateGrows, leftAt, Cursor.control]
    · simp [CoreUpdateGrows, atCommon]
    · simpa only [visible, List.filter_append, List.filter_cons, List.filter_nil, Bool.false_eq_true,
        ↓reduceIte, List.append_nil] using seenLeft
    · simpa only [visible, List.filter_append, List.filter_cons, List.filter_nil, Bool.false_eq_true,
        ↓reduceIte, List.append_nil] using seenRight

theorem collectionReturn (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    {left right last : State grow sig} {labels} (path : Prefix profile ready bindings first left labels last)
    (paired : HostFrame.Paired first second left right) (checkCursor : Cursor (E := core3 grow) (HostState sig))
    (leftAt : last.ctl = { checkCursor with frames := .prog first :: checkCursor.frames }.control (pure (.nat pointer)))
    (present : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkBody : first (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : second (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    (compared : ReachedCollectionTail profile ready bindings destination inst entries area output index pointer last) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    (∃ canonCursor, canonCursor.thread = checkCursor.thread ∧
      Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext) ∨
    (∃ leftLabels rightLabels other,
      CoreGrowthSteps profile ready dispatch left leftLabels { last with ctl := checkCursor.control (first (.nat pointer)) } ∧
      CoreGrowthSteps profile ready dispatch right rightLabels other ∧
      HostFrame.Paired first second { last with ctl := checkCursor.control (first (.nat pointer)) } other ∧
      visible leftLabels = labels ∧ visible rightLabels = labels) := by
  have cut := collectionReturnKeeping destination inst entries area output index pointer path paired checkCursor leftAt
    present sized checkNext canonNext checkBody canonBody (keep := fun _ => True) (by
      intro _ reference reachedBytes width size aligned fits live checked canonical checkStore canonStore checkHost canonHost
        same check canon thread finish next checkAt canonAt
      exact (compared reference reachedBytes width size aligned fits live checked canonical checkStore canonStore checkHost canonHost
        same check canon thread finish next checkAt canonAt).remember_true)
  rcases cut with ⟨cursor, thread, rest⟩ | common
  · exact .inl ⟨cursor, thread, rest.forget⟩
  · exact .inr common

private theorem chain {before middle after : State grow sig} {leading trailing : List (Label (core3 grow) (HostState sig))}
    (lhs : Steps profile ready (specDispatch ready (host (grow := grow) bindings)) before leading middle)
    (rhs : Steps profile ready (specDispatch ready (host (grow := grow) bindings)) middle trailing after) :
    Steps profile ready (specDispatch ready (host (grow := grow) bindings)) before (leading ++ trailing) after := by
  induction lhs with
  | refl => exact rhs
  | cons step _ ih => exact .cons step (ih rhs)

theorem collection (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index pointer : Nat) {initial left right last : State grow sig} {before seen}
    (cursor reached : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (prefixRun : CoreGrowthSteps profile ready (specDispatch ready (host (grow := grow) bindings)) initial before right)
    (checkedDestination : destination.check initial.store = .ok ()) {bytes : Nat}
    (sized : (core3 grow).memSize? initial.store.core destination.memory = some bytes)
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
    let call := collectionEntry destination inst area entries.length dispatch left cursor checkResume
    Prefix profile ready bindings checkResume call seen last →
    last.ctl = { reached with frames := .prog checkResume :: reached.frames }.control (pure (.nat pointer)) →
    ReachedCollectionTail profile ready bindings destination inst entries area output index pointer last →
    CollectionCut profile ready bindings checkResume canonResume left right
      { last with ctl := reached.control (checkResume (.nat pointer)) } reached checkNext canonNext seen := by
  dsimp only
  intro path returned compared
  have original := destination.check_width initial.store checkedDestination
  have atEntry := prefixRun.grows.memAddrType original
  obtain ⟨checkEnter, canonEnter, paired⟩ := PayloadPrefix.collection_install destination inst type element entries
    output index left right cursor checkNext canonNext same atEntry mode prepared checkAt canonAt
  have region := prefixRun.linked_region (destination.context inst) (start := 0) (length := 0)
    rfl original sized (by simp)
  obtain ⟨size, readySize, _, _⟩ := region.2.2
  have sameStore : left.store = right.store := by
    simpa only using congrArg (fun (config : State grow sig) => config.store) same
  have seenWidth : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width := sameStore ▸ atEntry
  have seenSize : (core3 grow).memSize? left.store.core destination.memory = some size := sameStore ▸ readySize
  rcases collectionReturn destination inst entries (layout destination.width element) output index pointer path paired
    reached returned seenWidth seenSize checkNext canonNext rfl rfl compared with joined | common
  · obtain ⟨other, thread, tail⟩ := joined
    exact .inl ⟨other, thread, tail.prepend checkEnter canonEnter rfl⟩
  · obtain ⟨checkLabels, canonLabels, other, lhs, rhs, still, checkSeen, canonSeen⟩ := common
    exact .inr ⟨_, _, other, chain checkEnter lhs.steps, chain canonEnter rhs.steps, still, checkSeen, canonSeen⟩

theorem collectionMemory (destination : RecordDestination) (inst : InstId) (type element : TypeOf) (entries : List Field)
    (output : Lower.Output) (index pointer : Nat) {origin : CStore (core3 grow)} {left right last : State grow sig} {seen}
    (cursor reached : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (growth : Core3.Grows origin.core right.store.core)
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width) {bytes : Nat}
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
    let call := collectionEntry destination inst area entries.length dispatch left cursor checkResume
    Prefix profile ready bindings checkResume call seen last →
    last.ctl = { reached with frames := .prog checkResume :: reached.frames }.control (pure (.nat pointer)) →
    (∀ item ∈ entries, MemoryChildRule profile ready dispatch destination inst item element) →
    CollectionCutKeeping profile ready bindings (fun store => Core3.Grows origin.core store.core)
      checkResume canonResume left right { last with ctl := reached.control (checkResume (.nat pointer)) }
      reached checkNext canonNext seen := by
  dsimp only
  intro path returned child
  have referenceWidth := growth.memAddrType memoryWidth
  obtain ⟨checkEnter, canonEnter, paired⟩ := PayloadPrefix.collection_install destination inst type element entries
    output index left right cursor checkNext canonNext same referenceWidth mode prepared checkAt canonAt
  obtain ⟨size, readySize, _⟩ := growth.memSize sized
  have sameStore : left.store = right.store := by
    simpa only using congrArg (fun (config : State grow sig) => config.store) same
  have seenWidth : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width :=
    sameStore ▸ referenceWidth
  have seenSize : (core3 grow).memSize? left.store.core destination.memory = some size := sameStore ▸ readySize
  have prior : Core3.Grows origin.core left.store.core := sameStore ▸ growth
  have cut := collectionReturnKeeping destination inst entries (layout destination.width element) output index pointer
    path paired reached returned seenWidth seenSize checkNext canonNext rfl rfl
    (keep := fun store => Core3.Grows origin.core store.core) (by
      intro callbackGrowth reference reachedBytes width reachedSize aligned fits live checked canonical checkStore canonStore
        checkHost canonHost same check canon thread finish next checkAt canonAt
      exact (CollectionTailKeepingAt.memory_entries destination inst element entries child output index pointer reachedBytes
        last reference width reachedSize aligned fits live checked canonical checkStore canonStore checkHost canonHost
        same check canon thread finish next checkAt canonAt).weaken (fun _ later => prior.trans (callbackGrowth.trans later)))
  rcases cut with joined | common
  · obtain ⟨referenceCursor, thread, tail⟩ := joined
    exact .inl ⟨referenceCursor, thread, tail.prepend checkEnter canonEnter rfl⟩
  · obtain ⟨checkLabels, canonLabels, other, lhs, rhs, still, checkSeen, canonSeen⟩ := common
    exact .inr ⟨_, _, other, chain checkEnter lhs.steps, chain canonEnter rhs.steps, still, checkSeen, canonSeen⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback

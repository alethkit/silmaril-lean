module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms

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

theorem syncLift {start last : State grow sig} {labels task thread frames rest} {entry : Task (core3 grow)}
    (focused : start.ctl = ⟨thread, .prog (syncLiftLoopBody ready task), frames⟩ :: rest)
    (found : ArenaField.tasks.get? start.store task = some entry) (waiting : entry.state ≠ .resolved)
    (agrees : ReadyAgreement ready start entry.inst)
    (path : Prefix profile ready bindings first { start with ctl := ⟨thread,
      .prog (syncLiftCandidates task (start.store.instCandidates (ready start.host) entry.inst)), frames⟩ :: rest }
      labels last) : Prefix profile ready bindings first start labels last := by
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
  · rw [HostFrame.Interior, atStart]
    refine ⟨?_, ?_⟩ <;> intro _ _ _ _ impossible <;> cases impossible
  · unfold HostFrame.Interior
    refine ⟨?_, ?_⟩ <;> intro _ _ _ _ impossible <;> cases impossible

private theorem classifyPop {left right : State grow sig} {thread value frames rest}
    (commonHost : HostState sig) (paired : ReturnFrame.Paired first second (HostFrame.replace left commonHost) right)
    (focused : left.ctl = ⟨thread, .prog (.pure value), .prog first :: frames⟩ :: rest) :
    ∃ otherFrames otherRest,
      right.ctl = ⟨thread, .prog (.pure value), .prog second :: otherFrames⟩ :: otherRest ∨
      (right.ctl = ⟨thread, .prog (.pure value), .prog first :: otherFrames⟩ :: otherRest ∧
       HostFrame.Paired first second { left with ctl := ⟨thread, .prog (first value), frames⟩ :: rest }
         { right with ctl := ⟨thread, .prog (first value), otherFrames⟩ :: otherRest }) := by
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
          | swap => exact ⟨_, _, .inl rfl⟩
          | same => exact ⟨_, _, .inr ⟨rfl, .mk (.cons (.mk below) tail) blocked⟩⟩

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
  obtain ⟨leftLabels, rightLabels, other, lhs, rhs, reached, seenLeft, seenRight⟩ := replay path paired
  obtain ⟨otherFrames, otherRest, atPop | ⟨atCommon, still⟩⟩ := classifyPop other.host reached leftAt
  · let canonCursor : Cursor (E := core3 grow) (HostState sig) := ⟨checkCursor.thread, otherFrames, otherRest⟩
    have region := lhs.linked_region (destination.context inst) (start := 0) (length := 0)
      rfl present sized (by simp)
    obtain ⟨_, reachedWidth, bytes, reachedSize, _, _⟩ := region
    have continued := PayloadPrefix.collection_return_at destination inst entries area output index pointer last other
      checkCursor canonCursor checkNext canonNext first second reached rfl leftAt atPop checkBody canonBody reachedSize
      (compared other bytes reachedWidth reachedSize)
    exact .inl ⟨canonCursor, rfl, continued.prepend lhs.steps rhs.steps (seenLeft.trans seenRight.symm)⟩
  · refine .inr ⟨leftLabels ++ [.tau], rightLabels ++ [.tau], _, lhs.append (.cons ?_ (.popProg leftAt) (.refl _)),
      rhs.append (.cons ?_ (.popProg atCommon) (.refl _)), still, ?_, ?_⟩
    · simp [CoreUpdateGrows, leftAt, Cursor.control]
    · simp [CoreUpdateGrows, atCommon]
    · simpa only [visible, List.filter_append, List.filter_cons, List.filter_nil, Bool.false_eq_true,
        ↓reduceIte, List.append_nil] using seenLeft
    · simpa only [visible, List.filter_append, List.filter_cons, List.filter_nil, Bool.false_eq_true,
        ↓reduceIte, List.append_nil] using seenRight

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
  obtain ⟨checkEnter, canonEnter, paired⟩ := PayloadPrefix.collection_install destination inst type element entries
    output index left right cursor checkNext canonNext same prefixRun checkedDestination mode prepared checkAt canonAt
  have original := destination.check_width initial.store checkedDestination
  have atEntry := prefixRun.grows.memAddrType original
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

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LinkedCallback

module

public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Component.Reference.Machine.Config.Thms

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.MachineReturnOccurrence

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Machine.StepDefs
  Silmaril.Wasm.Component.Machine.ReturnFrame Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
variable {dispatch : Call E → P E Host (Ret E)}

private theorem map_setSlot {Item Mapped : Type} (project : Item → Mapped)
    (slots : List (Option Item)) (slot : Nat) (value : Option Item) :
    (Config.setSlot slots slot value).map (Option.map project) =
      Config.setSlot (slots.map (Option.map project)) slot (value.map project) := by
  induction slot generalizing slots with
  | zero => cases slots <;> rfl
  | succ _ ih => cases slots <;> simp [Config.setSlot, ih]

private theorem savedAt_eq {cfg : Config E Host} {thread : ThreadId} {activation : Activation E Host}
    (found : cfg.cont? thread = some activation) :
    ((segmentStorage cfg).saved[thread.idx]?.join.getD []) = activation.segs := by
  cases look : cfg.conts[thread.idx]? <;>
    simp [Config.cont?, look, Option.join] at found
  subst_vars
  simp [segmentStorage, look]

private theorem head_read {Item : Type} {storage : List (List Item)} {segment : Nat} :
    storage[0]?.bind (·[segment]?) = (storage.headD [])[segment]? := by
  cases storage <;> simp

private theorem saved_read {storage : Stacks E Host} {slot segment : Nat} :
    segmentAt storage (.saved slot segment) = (savedAt storage slot)[segment]? := by
  unfold segmentAt savedAt
  cases found : storage.saved[slot]?.join <;> simp [found]

private theorem read_block {storage : Stacks E Host} {slot : Nat} {place reached : Location}
    (moved : place.block slot = some reached) : segmentAt (storage.block slot) reached = segmentAt storage place := by
  cases place with
  | active activation segment =>
    cases activation with
    | zero =>
      simp [Location.block] at moved
      subst reached
      simp [segmentAt, Stacks.block, Config.getElem?_setSlot_self, front, head_read]
    | succ activation =>
      simp [Location.block] at moved
      subst reached
      cases storage.active <;> simp [segmentAt, Stacks.block, *]
  | saved current segment =>
    by_cases same : current = slot
    · simp [Location.block, same] at moved
    · simp [Location.block, same] at moved
      subst reached
      simp [segmentAt, Stacks.block, Config.getElem?_setSlot_ne _ _ _ _ same]

private theorem read_resume (storage : Stacks E Host) (slot : Nat) (place : Location) :
    segmentAt (storage.resume slot) (place.resume slot) = segmentAt storage place := by
  cases place with
  | active _ _ => rfl
  | saved current segment =>
    by_cases same : current = slot
    · subst current
      have here : (Location.saved slot segment).resume slot = .active 0 segment := by simp [Location.resume]
      rw [here]
      exact saved_read.symm
    · simp [Location.resume, Stacks.resume, segmentAt, same, Config.getElem?_setSlot_ne _ _ _ _ same]

theorem read_follow {storage : Stacks E Host} {edit : Edit E Host} {place reached : Location}
    (moved : edit.follow place = some reached) : segmentAt (edit.apply storage) reached = segmentAt storage place := by
  cases edit with
  | block slot => exact read_block moved
  | resume slot =>
    have same : place.resume slot = reached := Option.some.inj moved
    subst reached
    exact read_resume _ _ _
  | switch fromSlot toSlot =>
    cases blocked : place.block fromSlot with
    | none => simp [Edit.follow, blocked] at moved
    | some intermediate =>
      simp [Edit.follow, blocked] at moved
      subst reached
      exact (read_resume _ _ _).trans (read_block blocked)
  | same =>
    cases place <;> simp [Edit.follow] at moved <;> subst reached <;> rfl
  | write slot frames =>
    cases place with
    | active _ _ => simp [Edit.follow] at moved; subst reached; rfl
    | saved current segment =>
      by_cases same : current = slot
      · simp [Edit.follow, same] at moved
      · simp [Edit.follow, same] at moved
        subst reached
        simp [segmentAt, Edit.apply, Config.getElem?_setSlot_ne _ _ _ _ same]
  | clear | enter =>
    cases place <;> simp [Edit.follow] at moved
    subst reached
    rfl
  | exit =>
    cases place with
    | active activation segment =>
      cases activation <;> simp [Edit.follow] at moved
      subst reached
      cases storage.active <;> simp [segmentAt, Edit.apply, *]
    | saved _ _ => simp [Edit.follow] at moved; subst reached; rfl
  | push frame =>
    cases place with
    | active activation segment =>
      cases activation <;> simp [Edit.follow] at moved <;> subst reached
      · simp [Edit.apply, segmentAt, front, head_read]
      · cases storage.active <;> simp [segmentAt, Edit.apply, *]
    | saved _ _ => simp [Edit.follow] at moved; subst reached; rfl
  | pop =>
    cases place with
    | active activation segment =>
      cases activation with
      | zero =>
        cases segment with
        | zero => simp [Edit.follow] at moved
        | succ segment =>
          simp [Edit.follow] at moved
          subst reached
          change (front storage).tail[segment]? = storage.active[0]?.bind (·[segment + 1]?)
          rw [head_read]
          change (front storage).tail[segment]? = (front storage)[segment + 1]?
          cases front storage <;> simp
      | succ _ =>
        simp [Edit.follow] at moved
        subst reached
        cases storage.active <;> simp [segmentAt, Edit.apply, *]
    | saved _ _ => simp [Edit.follow] at moved; subst reached; rfl

theorem step_edit {before after : Config E Host} {label : Label E Host}
    (run : Step profile ready dispatch before label after) :
    segmentStorage after = (transitionEdit before label).apply (segmentStorage before) := by
  cases run with
  | popProg focused => simp [transitionEdit, segmentStorage, Edit.apply, focused, front]
  | popCore focused =>
    simp [transitionEdit, segmentStorage, Edit.apply, focused, front]
  | threadExit focused => simp [transitionEdit, segmentStorage, Edit.apply, focused]
  | @hostDone result rest focused =>
    (cases rest <;> cases result <;> simp [transitionEdit, segmentStorage, Edit.apply, focused, hostFinish]);
      split <;> simp [Config.setCancel]
  | call focused => simp [transitionEdit, segmentStorage, Edit.apply, front, focused]
  | coreCallout focused called => simp [transitionEdit, segmentStorage, Edit.apply, front, focused, called]
  | newThread focused allocated =>
    simp [transitionEdit, segmentStorage, Edit.apply, focused, allocated, Config.setCont, map_setSlot,
      threadAct, Activation.ofProg]
  | block focused =>
    simp [transitionEdit, segmentStorage, Edit.apply, Stacks.block, front, focused, Config.setCont,
      map_setSlot, blockedAct]
  | resumeThread focused found =>
    simp only [transitionEdit, focused, Edit.apply, Stacks.resume, savedAt, savedAt_eq found]
    simp [segmentStorage, focused, Config.setCont, map_setSlot]
  | blockSwitch focused found =>
    have saved := savedAt_eq found
    simp only [segmentStorage, Config.setCont, map_setSlot, Option.map_some, blockedAct] at saved
    simp [transitionEdit, focused, Edit.apply, Stacks.resume, Stacks.block, savedAt, front, segmentStorage,
      Config.setCont, map_setSlot, blockedAct, saved]
  | trap _ | coreTrap _ _ | fault _ => rfl
  | hostInvoke _ _ | hostTick _ | hostCancel _ _ _ | hostRun _ => rfl
  | @emit _ obs _ _ _ focused =>
    cases obs <;> simp [transitionEdit, observe, Config.resolve, segmentStorage, Edit.apply, focused]
  | coreReturned focused done => simp [transitionEdit, done, segmentStorage, Edit.apply, focused]
  | callCore focused | coreInternal focused _ _ | get focused | modify focused
  | choose _ focused _ | currentThread focused | hostGet focused | hostSet focused =>
    simp [transitionEdit, segmentStorage, Edit.apply, focused]

theorem step_follow {before after : Config E Host} {label : Label E Host} {place reached : Location}
    (run : Step profile ready dispatch before label after) (moved : (transitionEdit before label).follow place = some reached) :
    segmentAt (segmentStorage after) reached = segmentAt (segmentStorage before) place := by
  rw [step_edit run]
  exact read_follow moved

theorem step_pop {before after : Config E Host} {label : Label E Host} {place : Location} {resume : Continuation E Host}
    (run : Step profile ready dispatch before label after)
    (occurs : segmentAt (segmentStorage before) place = some (.prog resume))
    (pops : (transitionEdit before label).pops place) : Popped before after label place resume := by
  have here : place = .active 0 0 := by
    generalize transitionEdit before label = edit at pops
    cases edit <;> cases place <;> try contradiction
    rename_i activation segment
    cases activation <;> cases segment <;> simp_all [Edit.pops]
  subst place
  cases run with
  | @popProg thread value actual frames rest focused =>
    have same : actual = resume := by simpa [segmentAt, segmentStorage, focused] using occurs
    subst actual
    exact ⟨rfl, rfl, thread, value, frames, rest, focused, rfl⟩
  | popCore focused => simp [segmentAt, segmentStorage, focused] at occurs
  | coreReturned focused done => simp [transitionEdit, focused, done, Edit.pops] at pops
  | coreCallout focused called => simp [transitionEdit, focused, called, Edit.pops] at pops
  | threadExit focused | hostDone focused | call focused | callCore focused | get focused | modify focused
  | newThread focused _ | block focused | blockSwitch focused _ | resumeThread focused _
  | currentThread focused | hostGet focused | hostSet focused => simp [transitionEdit, focused, Edit.pops] at pops
  | choose _ _ _ | coreInternal _ _ _ | emit _ | trap _ | coreTrap _ _ | fault _
  | hostInvoke _ _ | hostTick _ | hostCancel _ _ _ | hostRun _ => contradiction

theorem prefix_survives {before after : Config E Host} {labels : List (Label E Host)} {place reached : Location}
    (run : Prefix profile ready dispatch before place labels after reached) :
    Steps profile ready dispatch before labels after ∧
      segmentAt (segmentStorage after) reached = segmentAt (segmentStorage before) place := by
  induction run with
  | done => exact ⟨.refl _, rfl⟩
  | step head moved _ ih => exact ⟨.cons head ih.1, ih.2.trans (step_follow head moved)⟩

theorem first_loss {before after : Config E Host} {labels : List (Label E Host)} {place : Location}
    {resume : Continuation E Host} (occurs : segmentAt (segmentStorage before) place = some (.prog resume))
    (run : Steps profile ready dispatch before labels after) :
    (∃ reached, Prefix profile ready dispatch before place labels after reached) ∨
    ∃ leading label trailing atLoss next reached,
      labels = leading ++ label :: trailing ∧
      Prefix profile ready dispatch before place leading atLoss reached ∧
      Step profile ready dispatch atLoss label next ∧ Steps profile ready dispatch next trailing after ∧
      (transitionEdit atLoss label).follow reached = none ∧
      (Popped atLoss next label reached resume ∨ ¬ (transitionEdit atLoss label).pops reached) := by
  induction run generalizing place with
  | refl => exact .inl ⟨place, .done _ _⟩
  | @cons start next after label labels step rest ih =>
    cases moved : (transitionEdit start label).follow place with
    | none =>
      refine .inr ⟨[], label, labels, start, next, place, rfl, .done _ _, step, rest, moved, ?_⟩
      by_cases popped : (transitionEdit start label).pops place
      · exact .inl (step_pop step occurs popped)
      · exact .inr popped
    | some reached =>
      rcases ih ((step_follow step moved).trans occurs) with ⟨reached, tail⟩ |
        ⟨leading, loss, trailing, atLoss, afterLoss, marked, split, trail, cut, remainder, removed, kind⟩
      · exact .inl ⟨reached, .step step moved tail⟩
      · exact .inr ⟨label :: leading, loss, trailing, atLoss, afterLoss, marked, congrArg (List.cons label) split,
          .step step moved trail, cut, remainder, removed, kind⟩

end Silmaril.Proofs.Wasm.Component.Reference.MachineReturnOccurrence

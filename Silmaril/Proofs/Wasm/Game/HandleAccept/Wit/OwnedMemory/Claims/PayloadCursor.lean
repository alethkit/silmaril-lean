module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Sequence.Defs
public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Width.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (LocalIssue)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Machine.Config (core3 grow) Host} {trace : List (Label (core3 grow) Host)}

theorem check_width (destination : RecordDestination) (store : CStore (core3 grow))
    (checked : destination.check store = .ok ()) :
    (core3 grow).memAddrType? store.core destination.memory = some destination.width := by
  unfold RecordDestination.check at checked
  by_contra missing
  simp only [bne_iff_ne, ne_eq, missing, not_false_eq_true, ite_true] at checked
  contradiction

theorem memory_cursor (run : CoreGrowthSteps profile ready dispatch before trace after)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check before.store = .ok ())
    (storeField : Nat → Field → Nat → P (core3 grow) Host Unit)
    (field : Field) (fields : List Field) (cursor index : Nat)
    (finish : Unit → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (memorySequence (ptrType (destination.context inst))
      storeField (field :: fields) cursor index >>= finish), segments⟩ :: rest) :
    let area := layout destination.width field.type
    let ptr := alignTo cursor area.alignment
    CoreGrowthSteps profile ready dispatch after [.tau]
      { after with ctl := ⟨thread, .prog (do
          storeField index field ptr
          let result ← memorySequence (ptrType (destination.context inst)) storeField fields
            (ptr + area.size) (index + 1)
          finish result), segments⟩ :: rest } := by
  let next := fun width => do
    let area := layout width field.type
    let ptr := alignTo cursor area.alignment
    storeField index field ptr
    let result ← memorySequence (ptrType (destination.context inst)) storeField fields
      (ptr + area.size) (index + 1)
    finish result
  apply run.read_width (destination.context inst) rfl (check_width destination before.store checked) next
  simpa only [memorySequence, bind_assoc, next] using focused

theorem list_range_call (cx : LiftLowerContext (core3 grow)) (area : Layout) (count : Nat)
    (finish : Nat → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (allocateListRange cx area count >>= finish),
      segments⟩ :: rest) :
    let request := Call.reallocate cx 0 0 area.alignment.bytes (count * area.size)
    ∃ resume : Ret (core3 grow) → P (core3 grow) Host (Ret (core3 grow)),
      (∀ pointer, resume (.nat pointer) = (validateListRange cx area count pointer >>= finish)) ∧
      Step profile ready dispatch after .tau
        { after with ctl := ⟨thread, .prog (dispatch request), .prog resume :: segments⟩ :: rest } := by
  let resume : Ret (core3 grow) → P (core3 grow) Host (Ret (core3 grow)) := fun result =>
    (match result with
    | .nat pointer => pure pointer
    | _ => internal "late-bound call: expected Ret.nat") >>= fun pointer =>
    validateListRange cx area count pointer >>= finish
  refine ⟨resume, fun _ => rfl, ?_⟩
  have unfoldCall : (allocateListRange cx area count >>= finish) =
      .op (.call (.reallocate cx 0 0 area.alignment.bytes (count * area.size))) resume := by
    unfold allocateListRange allocate reallocate callNat callRet perform Prog.lift
    simp only [bind_assoc]
    apply congrArg (Prog.op (S := Eff (core3 grow) Host)
      (.call (.reallocate cx 0 0 area.alignment.bytes (count * area.size))))
    funext result
    cases result <;> rfl
  rw [unfoldCall] at focused
  exact Machine.Step.call focused

theorem list_range_body (destination : RecordDestination) (inst : InstId) (area : Layout)
    (count pointer : Nat) (store : CStore (core3 grow)) (host : Host) (thread : Option ThreadId) :
    Plain.runBody (validateListRange (destination.context inst) area count pointer) store host (some thread) =
      (store, host, if pointer ≠ alignTo pointer area.alignment then .error (.trapped .unalignedPointer)
        else match (core3 grow).memSize? store.core destination.memory with
        | none => .error (.trapped (.internal "dangling memory address"))
        | some size => if pointer + count * area.size ≤ size then .ok pointer
            else .error (.trapped .outOfBounds)) := by
  unfold validateListRange
  split
  · rename_i unaligned
    simp [trapIf, unaligned]
    rfl
  · rename_i aligned
    simp [trapIf, aligned]
    change Plain.runBody (.op .get (fun current =>
      (orTrap (.internal "dangling memory address") ((core3 grow).memSize? current.core destination.memory) >>=
        fun size => trapIf (decide (pointer + count * area.size > size)) .outOfBounds) >>=
        fun _ => pure pointer)) store host (some thread) = _
    rw [Plain.runBody]
    cases sized : (core3 grow).memSize? store.core destination.memory with
    | none => rfl
    | some size =>
      simp only [orTrap, pure_bind]
      by_cases bounds : pointer + count * area.size ≤ size
      · simp [trapIf, Nat.not_lt.mpr bounds, bounds]
        rfl
      · simp [trapIf, Nat.lt_of_not_ge bounds, bounds]
        rfl

theorem list_range_resume (destination : RecordDestination) (inst : InstId) (area : Layout)
    (count pointer : Nat) (finish : Nat → P (core3 grow) Host (Ret (core3 grow)))
    (resume : Ret (core3 grow) → P (core3 grow) Host (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= finish))
    {thread segments rest}
    (returned : after.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest) :
    let body := validateListRange (destination.context inst) area count pointer
    match (Plain.runBody body after.store after.host (some thread)).2.2 with
    | .ok value => ∃ labels, (∀ label ∈ labels, label = .tau) ∧
        Machine.Steps profile ready dispatch after labels
          { after with ctl := ⟨thread, .prog (finish value), segments⟩ :: rest }
    | .error (.trapped reason) => ∃ count, Machine.Steps profile ready dispatch after
        (List.replicate count .tau ++ [.trap reason]) (Machine.StepDefs.trapCfg after)
    | .error _ => False := by
  let body : P (core3 grow) Host Nat := validateListRange (destination.context inst) area count pointer
  let reached := { after with ctl := ⟨thread, .prog (body >>= finish), segments⟩ :: rest }
  have pop : Machine.Step profile ready dispatch after .tau reached := by
    have step := Machine.Step.popProg (prof := profile) (hr := ready) (dispatch := dispatch) returned
    rw [resumes] at step
    exact step
  have readOnly := list_range_body destination inst area count pointer after.store after.host thread
  change Plain.runBody body after.store after.host (some thread) = _ at readOnly
  dsimp only
  generalize answer : (Plain.runBody body after.store after.host (some thread)).2.2 = verdict
  have evaluation : Plain.runBody body after.store after.host (some thread) = (after.store, after.host, verdict) := by
    rw [← answer, readOnly]
  cases verdict with
  | ok value =>
    obtain ⟨labels, silent, tail⟩ := Plain.runBody_thread_steps body reached after.store after.host value
      finish thread segments rest profile ready dispatch rfl evaluation
    refine ⟨.tau :: labels, ?_, .cons pop tail⟩
    intro label member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · have tested := List.all_eq_true.mp silent label member
      cases label <;> first | rfl | contradiction
  | error issue =>
    cases issue with
    | trapped reason =>
      obtain ⟨count, tail⟩ := Plain.runBody_trap_steps body reached after.store after.host reason
        finish thread segments rest profile ready dispatch rfl evaluation
      exact ⟨count + 1, .cons pop tail⟩
    | _ =>
      rw [evaluation] at readOnly
      split at readOnly
      · cases readOnly
      · split at readOnly
        · cases readOnly
        · split at readOnly <;> cases readOnly

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor

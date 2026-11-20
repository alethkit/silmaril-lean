module

public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Context.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Dispatch.Defs
import Silmaril.Wasm.Component.Reference.Canon.Lift.Thms
import Silmaril.Wasm.Component.Reference.Engine.Core3.StepLaws.Grows.Defs
import Silmaril.Wasm.Component.Reference.Engine.Core3.Store.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Config (core3 grow) Host} {label : Label (core3 grow) Host}
  {trace : List (Label (core3 grow) Host)}

theorem step_grows (step : Step profile ready dispatch before label after)
    (updates : CoreUpdateGrows before) : Core3.Grows before.store.core after.store.core := by
  cases step <;> try exact Core3.Grows.refl _
  case hostDone =>
    unfold StepDefs.hostFinish
    split <;> exact Core3.Grows.refl _
  case coreInternal internal => exact Core3.internal_grows internal
  case modify focused => simpa only [CoreUpdateGrows, focused] using updates
  case newThread allocated =>
    cases allocated
    exact Core3.Grows.refl _
  case emit =>
    unfold StepDefs.observe
    split <;> exact Core3.Grows.refl _

theorem update_of_inv {thread segments rest} (program : P (core3 grow) Host (Ret (core3 grow)))
    (focused : before.ctl = ⟨thread, .prog program, segments⟩ :: rest)
    (preserves : P.Inv (fun store => Core3.Grows before.store.core store.core) program) :
    CoreUpdateGrows before := by
  rw [CoreUpdateGrows, focused]
  cases program with
  | pure => trivial
  | op op _ =>
    cases op <;> try trivial
    cases preserves with
    | op update _ => exact update _ (Core3.Grows.refl _)

theorem steps (run : CoreGrowthSteps profile ready dispatch before trace after) :
    Steps profile ready dispatch before trace after := by
  induction run with
  | refl => exact .refl _
  | cons _ step _ tail => exact .cons step tail

theorem of_core_steps (run : Steps profile ready dispatch before trace after)
    (coreOnly : ∀ label ∈ trace, label = .core) :
    CoreGrowthSteps profile ready dispatch before trace after ∧ after.host = before.host := by
  induction run with
  | refl => exact ⟨.refl _, rfl⟩
  | cons step _ tail =>
    have atCore := coreOnly _ (.head _)
    subst atCore
    obtain ⟨certified, hostEq⟩ := tail (fun label member => coreOnly label (.tail _ member))
    refine ⟨.cons ?_ step certified, hostEq.trans ?_⟩ <;> cases step
    · rename_i focused _ _ _
      simp [CoreUpdateGrows, focused]
    · rfl

theorem writeMemSt_grows (store : CStore (core3 grow)) (memory ptr : Nat) (bytes : ByteArray) :
    Core3.Grows store.core (writeMemSt memory ptr bytes store).core := by
  unfold writeMemSt
  split
  · rename_i wrote
    exact Core3.memWrite?_grows wrote
  · exact Core3.Grows.refl _

private theorem releaseLenders_core {E : CoreEngine} (store : CStore E) (lenders : List HandleObjId) :
    (lenders.foldl (fun current id => ArenaField.resHandles.modify current id
      fun handle => { handle with numLends := handle.numLends - 1 }) store).core = store.core := by
  induction lenders generalizing store with
  | nil => rfl
  | cons _ _ tail => exact tail _

private theorem deliverResolve_core {E : CoreEngine} (store : CStore E) (subtask : SubtaskId) :
    (store.deliverResolveSt subtask).core = store.core := by
  unfold CStore.deliverResolveSt
  split
  · rfl
  · exact releaseLenders_core _ _

private theorem takeWaitableEvent_core {E : CoreEngine} (store : CStore E) (waitable : Waitable) :
    (store.takeWaitableEventSt waitable).core = store.core := by
  cases waitable with
  | end_ endpoint =>
    simp only [CStore.takeWaitableEventSt, CStore.takeWaitableEvent]
    unfold takeEvent
    repeat' split
    all_goals first | rfl | (unfold deliver; split <;> rfl)
  | subtask subtask =>
    simp only [CStore.takeWaitableEventSt, CStore.takeWaitableEvent]
    repeat' split
    all_goals try rfl
    unfold CStore.subtaskEvent
    split
    · rfl
    · split <;> first | rfl | exact deliverResolve_core _ _

private theorem task_frame (base : CStore (core3 grow)) :
    Task.InvHyps (fun store : CStore (core3 grow) => Core3.Grows base.core store.core) := by
  constructor <;> intros
  all_goals try assumption
  case registerThread =>
    rename_i task thread store growth
    unfold CStore.registerThreadSt
    cases taskEntry : store.task? task with
    | none => exact growth
    | some info =>
      dsimp only
      split <;> exact growth
  case unregisterThread =>
    unfold CStore.unregisterThreadSt
    split <;> assumption

private theorem lift_frame (base : CStore (core3 grow)) :
    LiftHyps (fun store : CStore (core3 grow) => Core3.Grows base.core store.core) := by
  refine ⟨task_frame base, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro store inst index growth
      exact growth
    · intros; assumption
    · intros; assumption
  · constructor
    · intro memory ptr bytes store grows
      exact grows.trans (writeMemSt_grows store memory ptr bytes)
    · intro store handle growth
      exact growth
    · intro store inst entry growth
      exact growth
    all_goals intros; assumption
  all_goals try (intros; assumption)
  · intro waitable store grows
    simpa only [takeWaitableEvent_core] using grows

theorem realloc_local_grows (ready : HostReady Host) (host : HostImpl (core3 grow) Host)
    (base : CStore (core3 grow)) (context : LiftLowerContext (core3 grow))
    (old oldLen align newLen : Nat) :
    P.Inv (fun store => Core3.Grows base.core store.core)
      (specDispatch ready host (.reallocate context old oldLen align newLen)) :=
  P.Inv.reallocProg (lift_frame base) _ _ _ _ _ _ _

theorem grows (run : CoreGrowthSteps profile ready dispatch before trace after) :
    Core3.Grows before.store.core after.store.core := by
  induction run with
  | refl => exact .refl _
  | cons updates step _ tail => exact (step_grows step updates).trans tail

theorem append {middle : Config (core3 grow) Host} {suffix : List (Label (core3 grow) Host)}
    (prefixSteps : CoreGrowthSteps profile ready dispatch before trace middle)
    (suffixSteps : CoreGrowthSteps profile ready dispatch middle suffix after) :
    CoreGrowthSteps profile ready dispatch before (trace ++ suffix) after := by
  induction prefixSteps with
  | refl => exact suffixSteps
  | cons updates step _ tail => exact .cons updates step (tail suffixSteps)

theorem linked_region (run : CoreGrowthSteps profile ready dispatch before trace after)
    (context : LiftLowerContext (core3 grow)) {memory start length size : Nat} {width : AddrType}
    (linked : context.opts.memory = some memory)
    (present : (core3 grow).memAddrType? before.store.core memory = some width)
    (sized : (core3 grow).memSize? before.store.core memory = some size)
    (bounds : start + length ≤ size) :
    ptrTypeIn before.store context = width ∧ ptrTypeIn after.store context = width ∧
      ∃ reachedSize, (core3 grow).memSize? after.store.core memory = some reachedSize ∧
        size ≤ reachedSize ∧ start + length ≤ reachedSize := by
  have growth := grows run
  have reached := growth.memAddrType present
  obtain ⟨reachedSize, sized', larger⟩ := growth.memSize sized
  refine ⟨?_, ?_, reachedSize, sized', larger, bounds.trans larger⟩
  · simp [ptrTypeIn, CanonOpts.ptrType, linked, present]
  · change (core3 grow).memAddrType? after.store.core memory = some width at reached
    simp [ptrTypeIn, CanonOpts.ptrType, linked, reached]

end Silmaril.Proofs.Wasm.Component.Reference.MachineCoreGrowth

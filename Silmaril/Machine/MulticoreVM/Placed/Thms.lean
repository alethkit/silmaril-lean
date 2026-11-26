module

public import Mathlib.SetTheory.Cardinal.NatCard
public import Silmaril.Machine.MulticoreVM.Placed.Defs
public import Silmaril.Machine.MulticoreVM.Thms
import Silmaril.Semantics.ConcurrentTrace.Thms
import Silmaril.Proofs.Machine.MulticoreVM.Placed.Refinement

public section

namespace Silmaril.Machine.MulticoreVM.Placed

open Silmaril.Semantics.ConcurrentTrace (mapWord mapTrace mapTrace_ofWord)

universe u v

variable {CoreId ThreadId Core Thread Choice Event : Type u}
variable {CoreId' ThreadId' Event' : Type v}

/-- Each resident thread takes a slot on a present core. Thread IDs may be infinite. -/
theorem Config.resident_card_le_present [Finite CoreId] (cfg : Config CoreId ThreadId Core Thread) :
    Nat.card cfg.Resident ≤ Nat.card cfg.PresentCore :=
  Proofs.Machine.MulticoreVM.Placed.resident_card_le_present cfg

theorem Config.resident_card_le [Finite CoreId] (cfg : Config CoreId ThreadId Core Thread) :
    Nat.card cfg.Resident ≤ Nat.card CoreId :=
  cfg.resident_card_le_present.trans (Finite.card_subtype_le _)

@[simp] theorem threadWord_append (a b : TaggedWord CoreId ThreadId Event) :
    threadWord (a ++ b) = threadWord a ++ threadWord b := List.map_append

@[simp] theorem coreWord_append (a b : TaggedWord CoreId ThreadId Event) :
    coreWord (a ++ b) = coreWord a ++ coreWord b := List.map_append

/-- Typed relabeling commutes with the named thread projection. -/
@[simp] theorem threadWord_mapTaggedWord (core : CoreId → CoreId') (thread : ThreadId → ThreadId')
    (event : Event → Event') (word : TaggedWord CoreId ThreadId Event) :
    threadWord (mapTaggedWord core thread event word) = mapWord thread event (threadWord word) :=
  Proofs.Machine.MulticoreVM.Placed.threadWord_mapTaggedWord core thread event word

/-- The chronological core projection preserves the opaque marker under relabeling. -/
@[simp] theorem coreWord_mapTaggedWord (core : CoreId → CoreId') (thread : ThreadId → ThreadId')
    (event : Event → Event') (word : TaggedWord CoreId ThreadId Event) :
    coreWord (mapTaggedWord core thread event word) = mapWord core (Option.map event) (coreWord word) :=
  Proofs.Machine.MulticoreVM.Placed.coreWord_mapTaggedWord core thread event word

/-- Renaming the projected thread trace requires an injective thread map. -/
theorem threadTrace_mapTaggedWord (core : CoreId → CoreId') (thread : ThreadId → ThreadId')
    (injective : Function.Injective thread) (event : Event → Event')
    (word : TaggedWord CoreId ThreadId Event) :
    threadTrace (mapTaggedWord core thread event word) = mapTrace thread injective event (threadTrace word) := by
  simp only [threadTrace, threadWord_mapTaggedWord, mapTrace_ofWord]

@[simp] theorem threadWord_tagFragment (core : CoreId) (thread : ThreadId)
    (fragment : Fragment ThreadId Event) :
    threadWord (tagFragment core thread fragment) = nameFragment thread fragment :=
  Proofs.Machine.MulticoreVM.Placed.threadWord_tagFragment core thread fragment

@[simp] theorem coreWord_tagFragment (core : CoreId) (thread : ThreadId)
    (fragment : Fragment ThreadId Event) :
    coreWord (tagFragment core thread fragment) = fragment.map (fun
      | .event value => .event core (some value)
      | .sync _ => .event core none) :=
  Proofs.Machine.MulticoreVM.Placed.coreWord_tagFragment core thread fragment

/-- The abstract length counts instructions, including silent instructions. -/
theorem threadSchedule_length (schedule : Schedule CoreId ThreadId Choice) :
    (threadSchedule schedule).length = (schedule.filter fun a => a.threadDecision.isSome).length := by
  rw [threadSchedule, List.length_filterMap_eq_countP, List.countP_eq_length_filter]

theorem ofThreadStep_refines (step : Transition (ThreadId → Option Thread) ThreadId Choice Event) :
    (ofThreadStep (CoreId := CoreId) (Core := Core) step).Refines step :=
  fun {_ _ _ _ _ _} _ h => h.1

/-- Project a successful finite execution to a current-thread schedule, named word and final
thread store. Placement commands disappear, while even silent instructions take a step. -/
theorem Scheduled.refines [DecidableEq CoreId]
    {instruction : Instruction CoreId ThreadId Core Thread Choice Event}
    {step : Transition (ThreadId → Option Thread) ThreadId Choice Event}
    (refines : instruction.Refines step)
    {schedule : Schedule CoreId ThreadId Choice} {initial final : Config CoreId ThreadId Core Thread}
    {word : TaggedWord CoreId ThreadId Event} (run : Scheduled instruction schedule initial word final) :
    MulticoreVM.Scheduled step (threadSchedule schedule) initial.threads (threadWord word) final.threads :=
  Proofs.Machine.MulticoreVM.Placed.scheduled_refines refines run

/-- The projected named observation belongs to the abstract run at the filtered length. -/
theorem Scheduled.mem_threadRun [DecidableEq CoreId]
    {instruction : Instruction CoreId ThreadId Core Thread Choice Event}
    {step : Transition (ThreadId → Option Thread) ThreadId Choice Event}
    (refines : instruction.Refines step)
    {schedule : Schedule CoreId ThreadId Choice} {initial final : Config CoreId ThreadId Core Thread}
    {word : TaggedWord CoreId ThreadId Event} (run : Scheduled instruction schedule initial word final) :
    (final.threads, threadWord word) ∈ namedOutcomes
      (MulticoreVM.run step (schedule.filter fun a => a.threadDecision.isSome).length) initial.threads :=
  (mem_run_iff_exists_schedule _).mpr ⟨threadSchedule schedule, threadSchedule_length schedule,
    run.refines refines⟩

/-- The direct projected trace and the quotient of the abstract named projection agree. -/
theorem observeThreadQuotient_eq (outcome : TaggedOutcome CoreId ThreadId Core Thread Event) :
    observeThreadQuotient outcome = MulticoreVM.observeQuotient (forgetCore outcome) := rfl

/-- The two projection routes agree on any set of concrete outcomes. -/
theorem observeThreadQuotient_image (outcomes : Set (TaggedOutcome CoreId ThreadId Core Thread Event)) :
    observeThreadQuotient '' outcomes = MulticoreVM.observeQuotient '' (forgetCore '' outcomes) :=
  (Set.image_image MulticoreVM.observeQuotient forgetCore outcomes).symm

section Refinement

variable [DecidableEq CoreId]
variable {instruction : Instruction CoreId ThreadId Core Thread Choice Event}
variable {step : Transition (ThreadId → Option Thread) ThreadId Choice Event}

/-- Each projected named outcome is admitted by the projected abstract schedule. -/
theorem forgetCore_image_subset_scheduledOutcomes (refines : instruction.Refines step)
    (schedule : Schedule CoreId ThreadId Choice) (initial : Config CoreId ThreadId Core Thread) :
    forgetCore '' taggedOutcomes instruction schedule initial ⊆
      MulticoreVM.scheduledOutcomes step (threadSchedule schedule) initial.threads := by
  rintro _ ⟨_, concrete, rfl⟩
  exact Scheduled.refines refines concrete

/-- Each projected named outcome is admitted by the abstract runner at the filtered length. -/
theorem forgetCore_image_subset_namedOutcomes (refines : instruction.Refines step)
    (schedule : Schedule CoreId ThreadId Choice) (initial : Config CoreId ThreadId Core Thread) :
    forgetCore '' taggedOutcomes instruction schedule initial ⊆
      namedOutcomes (MulticoreVM.run step (schedule.filter fun a => a.threadDecision.isSome).length)
        initial.threads := by
  rintro _ ⟨_, concrete, rfl⟩
  exact Scheduled.mem_threadRun refines concrete

/-- Forward refinement on quotient outcomes for the projected schedule. -/
theorem observeThreadQuotient_image_subset_scheduledOutcomes (refines : instruction.Refines step)
    (schedule : Schedule CoreId ThreadId Choice) (initial : Config CoreId ThreadId Core Thread) :
    observeThreadQuotient '' taggedOutcomes instruction schedule initial ⊆
      MulticoreVM.observeQuotient ''
        MulticoreVM.scheduledOutcomes step (threadSchedule schedule) initial.threads := by
  rw [observeThreadQuotient_image]
  exact Set.image_mono (forgetCore_image_subset_scheduledOutcomes refines schedule initial)

/-- Forward refinement on pairs of final thread stores and concurrent traces. -/
theorem observeThreadQuotient_image_subset_run (refines : instruction.Refines step)
    (schedule : Schedule CoreId ThreadId Choice) (initial : Config CoreId ThreadId Core Thread) :
    observeThreadQuotient '' taggedOutcomes instruction schedule initial ⊆
      MulticoreVM.observeQuotient ''
        namedOutcomes (MulticoreVM.run step (schedule.filter fun a => a.threadDecision.isSome).length)
          initial.threads := by
  rw [observeThreadQuotient_image]
  exact Set.image_mono (forgetCore_image_subset_namedOutcomes refines schedule initial)

end Refinement

end Silmaril.Machine.MulticoreVM.Placed

module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Proofs

open Diamond (ValueSort dataPorts)

universe u w

variable {Data : Type u} {value : Data → Type w} {carried : List (ValueSort Data)} {out : ValueSort Data}
variable [BankDecidableEq value (dataPorts carried)]

private theorem mem_schedule {changed : Prop} [Decidable changed] {job task : Task} {pending : List Task}
    (old : job ∈ pending) : job ∈ schedule changed task pending := by
  unfold schedule
  split <;> simp [old]

private theorem triggered_mem {changed : Prop} [Decidable changed] {task : Task} {pending : List Task}
    (trigger : changed) : task ∈ schedule changed task pending := by
  by_cases present : task ∈ pending <;> simp [schedule, trigger, present]

theorem mem_wake {old new : State value carried out} {job : Task} {pending : List Task}
    (h : job ∈ pending) : job ∈ wake old new pending :=
  mem_schedule (mem_schedule (mem_schedule h))

theorem changed_mem_wake {old new : State value carried out} {job : Task} {pending : List Task}
    (changed : dependencies new job ≠ dependencies old job) :
    job ∈ wake old new pending := by
  cases job with
  | control => exact mem_schedule (mem_schedule (triggered_mem changed))
  | phi => exact mem_schedule (triggered_mem changed)
  | result => exact triggered_mem changed

theorem wake_same (state : State value carried out) (pending : List Task) :
    wake state state pending = pending := by
  simp [wake, scheduleChanged, schedule]

private theorem scheduleChanged_length (old new : State value carried out) (job : Task) (pending : List Task) :
    (scheduleChanged old new job pending).length ≤ pending.length + 1 := by
  unfold scheduleChanged schedule
  split <;> simp

theorem wake_length (old new : State value carried out) (pending : List Task) :
    (wake old new pending).length ≤ pending.length + 3 := by
  let first := scheduleChanged old new .control pending
  let second := scheduleChanged old new .phi first
  have a := scheduleChanged_length old new .control pending
  have b := scheduleChanged_length old new .phi first
  have c := scheduleChanged_length old new .result second
  change first.length ≤ pending.length + 1 at a
  change second.length ≤ first.length + 1 at b
  change (scheduleChanged old new .result second).length ≤ pending.length + 3
  omega

private theorem scheduleChanged_nodup (old new : State value carried out) (job : Task) {pending : List Task}
    (nodup : pending.Nodup) : (scheduleChanged old new job pending).Nodup := by
  unfold scheduleChanged schedule
  split
  · rename_i triggered
    simp [List.nodup_append, nodup]
    exact fun _ mem eq => triggered.2 (eq ▸ mem)
  · exact nodup

theorem wake_nodup (old new : State value carried out) {pending : List Task} (nodup : pending.Nodup) :
    (wake old new pending).Nodup :=
  scheduleChanged_nodup old new .result
    (scheduleChanged_nodup old new .phi (scheduleChanged_nodup old new .control nodup))

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Proofs

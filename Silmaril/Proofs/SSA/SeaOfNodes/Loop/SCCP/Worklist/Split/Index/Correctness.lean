module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Thms
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Proofs

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {value : Data → Type w}

/-- A direct carried read has singleton support for exactly the fact it reads. -/
private theorem numbered_read {n : Nat} {ports : List (Ty Data)} {t : Ty Data}
    (number : Fin ports.length → Fin n) (port : Port ports t)
    (left right : BankFacts value ports) :
    ∃ i, (Phi.Support.numberedPorts ports number).get port = {number i} ∧
      ((bankTuple left).get port = (bankTuple right).get port ↔ left i = right i) := by
  induction port with
  | head => exact ⟨0, rfl, Iff.rfl⟩
  | tail port ih =>
    obtain ⟨i, support, same⟩ := ih (fun j => number j.succ)
      (fun j => left j.succ) (fun j => right j.succ)
    exact ⟨i.succ, support, same⟩

private theorem arg_eq_iff {ports captures : List (Ty Data)} {t : Ty Data}
    (captured : Tuple (Fact value) captures) (port : Port (captures ++ ports) t)
    (left right : BankFacts value ports) :
    (appendTuple (bankTuple left) captured).get port = (appendTuple (bankTuple right) captured).get port ↔
      ∀ i ∈ (appendTuple (Phi.Support.numberedPorts ports id)
        (Phi.Support.emptyPorts ports.length captures)).get port, left i = right i := by
  induction captured with
  | nil =>
    obtain ⟨i, support, same⟩ := numbered_read (ports := ports) id port left right
    change (bankTuple left).get port = (bankTuple right).get port ↔
      ∀ j ∈ (Phi.Support.numberedPorts ports id).get port, left j = right j
    rw [support]
    simpa using same
  | cons head tail ih =>
    cases port with
    | head =>
      change head = head ↔ ∀ i ∈ (∅ : Finset (Fin ports.length)), left i = right i
      simp
    | tail port => exact ih port

variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {m : Model.{u, v, w} Op}
variable {input : Tuple (Fact m.value) (dataPorts inputs)}

/-- Changed marks or a changed supported field under feedback account for exactly
the differences in the reference Φ watch key. -/
private theorem watched_eq_iff (old new : State m.value carried out) (dst : Phi.Job carried) :
    Phi.dependencies m g input new dst = Phi.dependencies m g input old dst ↔
      (incomingIndex .entry ∈ old.1 ↔ incomingIndex .entry ∈ new.1) ∧
      (incomingIndex .backedge ∈ old.1 ↔ incomingIndex .backedge ∈ new.1) ∧
      (incomingIndex .backedge ∈ new.1 →
        ∀ field ∈ Phi.feedbackSupport g dst, new.2.1 field = old.2.1 field) := by
  have entry :
      ((decide (incomingIndex .entry ∈ new.1)) = (decide (incomingIndex .entry ∈ old.1))) ↔
        (incomingIndex .entry ∈ old.1 ↔ incomingIndex .entry ∈ new.1) := by
    by_cases hn : incomingIndex .entry ∈ new.1 <;> by_cases ho : incomingIndex .entry ∈ old.1 <;> simp [hn, ho]
  simp only [Phi.dependencies, Prod.mk.injEq, entry]
  apply and_congr_right
  intro _
  by_cases hn : incomingIndex .backedge ∈ new.1 <;> by_cases ho : incomingIndex .backedge ∈ old.1
  · cases wire : Phi.wireAt (g.phiInputs .backedge) dst with
    | arg port =>
      simpa [hn, ho, wire, Phi.feedbackSupport, Phi.Support.wire, Phi.Support.read, Phi.Support.headerPorts]
        using arg_eq_iff input port new.2.1 old.2.1
    | output node port =>
      simp [hn, ho, Phi.Support.restrictBank_eq_iff]
  all_goals simp [hn, ho]

variable [BankDecidableEq m.value (dataPorts carried)]

theorem mem_destinations_iff (index : Index g) (old new : State m.value carried out) (dst : Phi.Job carried) :
    dst ∈ index.destinations old new ↔ Phi.dependencies m g input new dst ≠ Phi.dependencies m g input old dst := by
  rw [ne_eq, watched_eq_iff]
  by_cases marks : (incomingIndex .entry ∈ old.1 ↔ incomingIndex .entry ∈ new.1) ∧
      (incomingIndex .backedge ∈ old.1 ↔ incomingIndex .backedge ∈ new.1)
  · obtain ⟨entry, feedback⟩ := marks
    by_cases enabled : incomingIndex .backedge ∈ new.1
    · simp [Index.destinations, entry, feedback, enabled, Finset.mem_biUnion, index.mem_readers]
      constructor
      · rintro ⟨field, changed, read⟩
        exact ⟨field, read, changed⟩
      · rintro ⟨field, read, changed⟩
        exact ⟨field, changed, read⟩
    · simp [Index.destinations, entry, feedback, enabled]
  · simp [Index.destinations, marks, ← and_assoc]

theorem wake_eq (index : Index g) (old new : State m.value carried out) (pending : List (Task carried)) :
    Index.wake m index old new pending = Split.wake m g input old new pending := by
  have ordered :
      (index.destinations old new).sort.filter (fun dst => !pending.contains (.phi dst)) =
        (List.finRange (dataPorts carried).length).filter (fun dst =>
          !pending.contains (.phi dst) && decide (Phi.dependencies m g input new dst ≠
            Phi.dependencies m g input old dst)) := by
    apply List.SortedLT.eq_of_mem_iff
    · exact ((Finset.sortedLT_sort (index.destinations old new)).pairwise.filter _).sortedLT
    · exact ((List.sortedLT_finRange _).pairwise.filter _).sortedLT
    · intro dst
      simp only [List.mem_filter, Finset.mem_sort, List.mem_finRange, true_and, Bool.and_eq_true,
        decide_eq_true_eq]
      rw [mem_destinations_iff (m := m) (input := input)]
      exact and_comm
  unfold Index.wake Split.wake FIFO.wake Split.jobs
  simp only [List.cons_append, List.filter_cons, List.filter_append, List.filter_map, List.filter_nil,
    Function.comp_def, Split.dependencies, Bool.and_true, ordered]
  rfl

theorem step_eq (index : Index g) (job : Task carried) (state : State m.value carried out)
    (pending : List (Task carried)) :
    Index.step m input index job state pending = Split.step m g input job state pending :=
  congrArg (Prod.mk (Split.update m g input job state)) (wake_eq index state _ pending)

theorem runSteps_eq (index : Index g) :
    Index.runSteps m input index = Split.runSteps m g input := by
  have stepSame := funext fun job => funext fun state => funext fun pending =>
    step_eq (m := m) (input := input) index job state pending
  rw [Index.runSteps, Split.runSteps, stepSame]

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Proofs

module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.Defs
import Silmaril.Machine.SqliteVfs.ReadSplit.RangeLocal.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.RangeAgreement

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot (ReadsSnapshot)
open Silmaril.Machine.SqliteVfs.ReadSplit.RangeLocal (read_result_transport)

private theorem readsSnapshot_of_range_agreement {State : Type} (handler : Handler State)
    (before after : Bytes) (handle : Handle) (start : State) (offset : Nat)
    (counts : List Nat) (positive : ∀ n ∈ counts, 0 < n)
    (agree : ∀ i, i < counts.sum → before[offset + i]? = after[offset + i]?)
    (reads : ReadsSnapshot handler before handle start offset counts) :
    ReadsSnapshot handler after handle start offset counts := by
  induction counts generalizing start offset with
  | nil => exact trivial
  | cons count rest ih =>
    simp only [ReadsSnapshot] at reads ⊢
    have firstRange : ∀ i, i < count → before[offset + i]? = after[offset + i]? := by
      intro i inside
      apply agree
      simp only [List.sum_cons]
      omega
    have remainingRange : ∀ i, i < rest.sum →
        before[offset + count + i]? = after[offset + count + i]? := by
      intro i inside
      simpa only [Nat.add_assoc] using agree (count + i) (by simpa using inside)
    exact ⟨read_result_transport (positive count (by simp))
        (fun i inside => (firstRange i inside).symm) reads.1,
      ih _ _ (fun n member => positive n (List.mem_cons_of_mem _ member)) remainingRange reads.2⟩

/-- A positive fragment schedule has the same reference contract for two
snapshots agreeing on the requested optional bytes, regardless of their
contents outside that interval. -/
theorem readsSnapshot_iff_of_range_agreement {State : Type} (handler : Handler State)
    (before after : Bytes) (handle : Handle) (start : State) (offset : Nat)
    (counts : List Nat) (positive : ∀ n ∈ counts, 0 < n)
    (agree : ∀ i, i < counts.sum → before[offset + i]? = after[offset + i]?) :
    ReadsSnapshot handler before handle start offset counts ↔
      ReadsSnapshot handler after handle start offset counts :=
  ⟨readsSnapshot_of_range_agreement handler before after handle start offset counts positive agree,
    readsSnapshot_of_range_agreement handler after before handle start offset counts positive
      (fun i inside => (agree i inside).symm)⟩

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.RangeAgreement

module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.Defs

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.RangeAgreement

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews (ReadsAgreeingViews)

private theorem of_reference_range_agreement {State : Type} (handler : Handler State)
    (view : State → Bytes) (before after : Bytes) (handle : Handle)
    (start : State) (offset : Nat) (counts : List Nat)
    (agree : ∀ i, i < counts.sum → before[offset + i]? = after[offset + i]?)
    (reads : ReadsAgreeingViews handler view before handle start offset counts) :
    ReadsAgreeingViews handler view after handle start offset counts := by
  induction counts generalizing start offset with
  | nil => exact trivial
  | cons count rest ih =>
    simp only [ReadsAgreeingViews] at reads ⊢
    obtain ⟨positive, current, actualRead, remaining⟩ := reads
    have first : ∀ i, i < count → after[offset + i]? = (view start)[offset + i]? := by
      intro i inside
      have bounded := Nat.lt_of_lt_of_le inside (Nat.le_add_right count rest.sum)
      have same := agree i (by simpa only [List.sum_cons] using bounded)
      exact same.symm.trans (current i inside)
    have tail : ∀ i, i < rest.sum →
        before[offset + count + i]? = after[offset + count + i]? := by
      intro i inside
      have bounded := Nat.add_lt_add_left inside count
      simpa only [Nat.add_assoc] using agree (count + i) (by simpa only [List.sum_cons] using bounded)
    exact ⟨positive, first, actualRead, ih _ _ tail remaining⟩

/-- The same actual calls and per-call view contracts can be checked
against either reference if their optional bytes agree on the schedule's range. -/
theorem readsAgreeingViews_iff_of_reference_range_agreement {State : Type} (handler : Handler State)
    (view : State → Bytes) (before after : Bytes) (handle : Handle)
    (start : State) (offset : Nat) (counts : List Nat)
    (agree : ∀ i, i < counts.sum → before[offset + i]? = after[offset + i]?) :
    ReadsAgreeingViews handler view before handle start offset counts ↔
      ReadsAgreeingViews handler view after handle start offset counts :=
  ⟨of_reference_range_agreement handler view before after handle start offset counts agree,
    of_reference_range_agreement handler view after before handle start offset counts
      (fun i inside => (agree i inside).symm)⟩

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.ReferenceSnapshot.AgreeingViews.RangeAgreement

module
public import Silmaril.Formats.Sqlite.VirtualTable.Thms
public import Silmaril.Formats.Sqlite.VirtualTable.Backed.Defs

public section
namespace Silmaril.Proofs.Formats.Sqlite.VirtualTable.Backed
open Silmaril.Formats.Sqlite.VirtualTable
open Silmaril.Formats.Sqlite.VirtualTable.Backed

private theorem match_lower (dir : Direction) (lo hi : Int64) (row : Row 1)
    (h : (query dir lo hi).matches (fun _ => true) row = true) :
    Operator.ge.test row.rowid lo = true := by
  change (Operator.ge.test row.rowid lo && (Operator.lt.test row.values[0] hi && true)) = true at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem candidates_honest (snapshot : Snapshot 1) (dir : Direction) (lo hi : Int64) :
    Honest (query dir lo hi) (plan dir) snapshot (candidates snapshot dir lo) := by
  have perm : (candidates snapshot dir lo).Perm
      (snapshot.rows.filter fun row => Operator.ge.test row.rowid lo) :=
    List.mergeSort_perm ..
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro row h
    exact (List.mem_filter.mp (perm.subset h)).1
  · exact (perm.symm.map Row.rowid).nodup
      (snapshot.uniqueRowids.sublist (List.filter_sublist.map _))
  · apply (perm.filter _).trans
    rw [Query.matchingRows, List.filter_filter]
    apply List.Perm.of_eq
    apply List.filter_congr
    intro row _
    cases h : (query dir lo hi).matches (fun _ => true) row
    · simp
    · simp [match_lower dir lo hi row h]
  · intro row h
    have lower := (List.mem_filter.mp (perm.subset h)).2
    change (Operator.ge.test row.rowid lo && (true && true)) =
      true
    simp [lower]
  · intro _ requested got
    change some dir = some requested at got
    cases got
    exact Direction.sorted dir _

theorem startQuery_eq (snapshot : Snapshot 1) (dir : Direction) (lo hi : Int64) :
    (table snapshot).startQuery (query dir lo hi) =
      .ok (plan dir, .scanning (candidates snapshot dir lo)) := by
  cases dir <;> rfl

theorem query_correct (snapshot : Snapshot 1) (dir : Direction) (lo hi : Int64) :
    (table snapshot).run (query dir lo hi) = .ok ((query dir lo hi).reference snapshot) := by
  have honest := candidates_honest snapshot dir lo hi
  simp [Table.run, startQuery_eq, bind, Except.bind, Cursor.scanRows, pure, Except.pure,
    finish_eq_reference honest rfl]

end Silmaril.Proofs.Formats.Sqlite.VirtualTable.Backed

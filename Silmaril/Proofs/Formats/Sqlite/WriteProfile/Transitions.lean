module

public import Silmaril.Formats.Sqlite.WriteProfile.Defs

public section
namespace Silmaril.Proofs.Formats.Sqlite.WriteProfile

open Silmaril.Formats.Sqlite.WriteProfile

theorem readTable_unique (snapshot : Snapshot) : snapshot.readTable.Unique := by
  have perm := (List.mergeSort_perm snapshot.rows
    (fun a b => decide (a.id.toInt ≤ b.id.toInt))).map Row.id
  have unique : (snapshot.orderedRows.map Row.id).Nodup := perm.nodup_iff.mpr snapshot.unique
  change ((snapshot.orderedRows.map Row.entry).map Prod.fst).Nodup
  rw [List.map_map, List.nodup_iff_pairwise_ne]
  have lifted : ((snapshot.orderedRows.map Row.id).map Int64.toInt).Pairwise (· ≠ ·) :=
    unique.map Int64.toInt (fun _ _ different same => different (Int64.toInt.inj same))
  simpa only [List.map_map, Function.comp_def, Row.entry] using lifted

theorem readTable_ordered (snapshot : Snapshot) :
    snapshot.readTable.entries.Pairwise (fun a b => a.1 ≤ b.1) := by
  have ordered := List.pairwise_mergeSort
    (le := fun (a b : Row) => decide (a.id.toInt ≤ b.id.toInt))
    (fun _ _ _ left right => decide_eq_true (Int.le_trans (of_decide_eq_true left)
      (of_decide_eq_true right)))
    (fun a b => by cases Int.le_total a.id.toInt b.id.toInt with
                   | inl h => simp [h]
                   | inr h => simp [h]) snapshot.rows
  exact ordered.map Row.entry (fun _ _ h => of_decide_eq_true h)

theorem readTable_row (snapshot : Snapshot) {entry : Int × List Silmaril.Formats.Sqlite.Value}
    (member : entry ∈ snapshot.readTable.entries) :
    ∃ id amount : Int64, entry = (id.toInt, [.integer id, .integer amount]) := by
  change entry ∈ snapshot.orderedRows.map Row.entry at member
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
  exact ⟨row.id, row.amount, rfl⟩

theorem insert_rows (snapshot : Snapshot) {id value : Int64} {edited : Edited}
    (run : snapshot.apply (.insert (.integer id) (.integer value)) = .ok edited) :
    edited.snapshot.rows = ⟨id, value⟩ :: snapshot.rows ∧ edited.changed = 1 := by
  change snapshot.insert id value = .ok edited at run
  by_cases present : snapshot.has id
  · simp [Snapshot.insert, present] at run
  · simp [Snapshot.insert, present] at run
    cases run
    exact ⟨rfl, rfl⟩

theorem update_rows (snapshot : Snapshot) {id value : Int64} {edited : Edited}
    (run : snapshot.apply (.update (.integer id) (.integer value)) = .ok edited) :
    edited.snapshot.rows =
      (if snapshot.has id then snapshot.rows.map (replace id value) else snapshot.rows) ∧
    edited.changed = (if snapshot.has id then 1 else 0) := by
  change snapshot.update id (some value) = .ok edited at run
  by_cases present : snapshot.has id <;>
    simp [Snapshot.update, present] at run ⊢ <;>
    cases run <;> exact ⟨rfl, rfl⟩

theorem delete_rows (snapshot : Snapshot) {id : Int64} {edited : Edited}
    (run : snapshot.apply (.delete (.integer id)) = .ok edited) :
    edited.snapshot.rows = snapshot.rows.filter (fun row => row.id != id) ∧
    edited.changed = (if snapshot.has id then 1 else 0) := by
  change Except.ok (snapshot.erase id) = .ok edited at run
  cases run
  exact ⟨rfl, rfl⟩

theorem error_preserves (state : State) {command : Command} {error : Error}
    (failure : (step state command).result = .error error) :
    (step state command).state = state := by
  cases command with
  | edit edit => cases edited : state.visible.apply edit <;> simp_all [step]
  | begin => cases pending : state.pending <;> simp_all [step]
  | commit => cases pending : state.pending <;> simp_all [step]
  | rollback => cases pending : state.pending <;> simp_all [step]

theorem autocommit_edit (state : State) {edit : Edit} {after : Edited}
    (inactive : state.pending = none)
    (accepted : state.committed.apply edit = .ok after) :
    step state (.edit edit) =
      ⟨⟨after.snapshot, none⟩, .ok (.changed after.changed)⟩ := by
  simp [step, State.visible, inactive, accepted]

theorem pending_edit (state : State) {before : Snapshot} {edit : Edit} {after : Edited}
    (pending : state.pending = some before)
    (accepted : before.apply edit = .ok after) :
    step state (.edit edit) =
      ⟨⟨state.committed, some after.snapshot⟩, .ok (.changed after.changed)⟩ := by
  simp [step, State.visible, pending, accepted]

theorem rollback (state : State) {snapshot : Snapshot}
    (pending : state.pending = some snapshot) :
    step state .rollback = ⟨⟨state.committed, none⟩, .ok .transaction⟩ := by
  simp [step, pending]

theorem commit (state : State) {snapshot : Snapshot}
    (pending : state.pending = some snapshot) :
    step state .commit = ⟨⟨snapshot, none⟩, .ok .transaction⟩ := by
  simp [step, pending]

end Silmaril.Proofs.Formats.Sqlite.WriteProfile

module

public import Silmaril.Formats.Sqlite.WriteProfile.Defs
import Silmaril.Proofs.Formats.Sqlite.WriteProfile.Transitions

public section
namespace Silmaril.Formats.Sqlite.WriteProfile

theorem readTable_unique (snapshot : Snapshot) : snapshot.readTable.Unique :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.readTable_unique snapshot

theorem readTable_ordered (snapshot : Snapshot) :
    snapshot.readTable.entries.Pairwise (fun a b => a.1 ≤ b.1) :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.readTable_ordered snapshot

theorem readTable_row (snapshot : Snapshot) {entry : Int × List Silmaril.Formats.Sqlite.Value}
    (member : entry ∈ snapshot.readTable.entries) :
    ∃ id amount : Int64, entry = (id.toInt, [.integer id, .integer amount]) :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.readTable_row snapshot member

theorem insert_rows (snapshot : Snapshot) {id value : Int64} {edited : Edited}
    (run : snapshot.apply (.insert (.integer id) (.integer value)) = .ok edited) :
    edited.snapshot.rows = ⟨id, value⟩ :: snapshot.rows ∧ edited.changed = 1 :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.insert_rows snapshot run

theorem update_rows (snapshot : Snapshot) {id value : Int64} {edited : Edited}
    (run : snapshot.apply (.update (.integer id) (.integer value)) = .ok edited) :
    edited.snapshot.rows =
      (if snapshot.has id then snapshot.rows.map (replace id value) else snapshot.rows) ∧
    edited.changed = (if snapshot.has id then 1 else 0) :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.update_rows snapshot run

theorem delete_rows (snapshot : Snapshot) {id : Int64} {edited : Edited}
    (run : snapshot.apply (.delete (.integer id)) = .ok edited) :
    edited.snapshot.rows = snapshot.rows.filter (fun row => row.id != id) ∧
    edited.changed = (if snapshot.has id then 1 else 0) :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.delete_rows snapshot run

theorem error_preserves (state : State) {command : Command} {error : Error}
    (failure : (step state command).result = .error error) :
    (step state command).state = state :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.error_preserves state failure

theorem autocommit_edit (state : State) {edit : Edit} {after : Edited}
    (inactive : state.pending = none)
    (accepted : state.committed.apply edit = .ok after) :
    step state (.edit edit) =
      ⟨⟨after.snapshot, none⟩, .ok (.changed after.changed)⟩ :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.autocommit_edit state inactive accepted

theorem pending_edit (state : State) {before : Snapshot} {edit : Edit} {after : Edited}
    (pending : state.pending = some before)
    (accepted : before.apply edit = .ok after) :
    step state (.edit edit) =
      ⟨⟨state.committed, some after.snapshot⟩, .ok (.changed after.changed)⟩ :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.pending_edit state pending accepted

theorem rollback (state : State) {snapshot : Snapshot}
    (pending : state.pending = some snapshot) :
    step state .rollback = ⟨⟨state.committed, none⟩, .ok .transaction⟩ :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.rollback state pending

theorem commit (state : State) {snapshot : Snapshot}
    (pending : state.pending = some snapshot) :
    step state .commit = ⟨⟨snapshot, none⟩, .ok .transaction⟩ :=
  Silmaril.Proofs.Formats.Sqlite.WriteProfile.commit state pending

end Silmaril.Formats.Sqlite.WriteProfile

module

public import Silmaril.Formats.Sqlite.Shell.Defs

public section

open Silmaril.Formats.Sqlite

namespace Silmaril.Proofs.Formats.Sqlite.Shell.Seek

private theorem dropped_head_get (key : Int) (entries : List (Int × List Value)) :
    ((entries.dropWhile fun entry => entry.1 != key).head?).map Prod.snd =
      BTree.Abstract.lookupList key entries := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨other, row⟩
    by_cases same : other = key
    · simp [List.dropWhile, BTree.Abstract.lookupList, same]
    · have skip : (other != key) = true := by simpa using same
      simpa [List.dropWhile, BTree.Abstract.lookupList, same, skip] using ih

private theorem dropped_head_model (table : Vdbe.Table) (key : Int64) :
    ((table.entries.dropWhile fun entry => entry.1 != key.toInt).head?).map Prod.snd =
      table.get key.toInt :=
  (dropped_head_get key.toInt table.entries).trans (table.get_eq _).symm

private theorem run_halted (database : Vdbe.Database) (program : Vdbe.Program)
    (fuel : Nat) (state : Vdbe.State) (halted : state.halted.isSome = true) :
    Vdbe.run database program fuel state = .halted state := by
  cases fuel <;> simp [Vdbe.run, halted]

/-- The existing point-query program returns no rows on an absent key. -/
theorem execute_seek_none (table : Vdbe.Table) (key : Int64)
    (missing : table.get key.toInt = none) :
    Shell.execute table { columns := [.id, .amount], key := some key } = .ok ⟨["id", "amount"], []⟩ := by
  have observations := dropped_head_model table key
  have dropped : table.entries.dropWhile (fun entry => entry.1 != key.toInt) = [] := by
    cases rest : table.entries.dropWhile (fun entry => entry.1 != key.toInt) with
    | nil => rfl
    | cons entry tail => simp [rest, missing] at observations
  unfold Shell.execute
  rw [Nat.add_comm 7 (4 * table.entries.length)]
  simp [Shell.seek, Vdbe.run, Vdbe.step, Vdbe.execute, Vdbe.State.initial,
    Vdbe.State.advance, Vdbe.State.write, Vdbe.State.setCursor, Vdbe.State.seekCursor,
    Vdbe.State.jump, Shell.Column.name, dropped]
  rfl

/-- The actual seek program returns the exact signed key and amount of the
first selected well-typed row. -/
theorem execute_seek_some (table : Vdbe.Table) (key amount : Int64)
    (found : table.get key.toInt = some [.integer key, .integer amount]) :
    Shell.execute table { columns := [.id, .amount], key := some key } = .ok ⟨["id", "amount"], [[key.toInt, amount.toInt]]⟩ := by
  have observations := dropped_head_model table key
  obtain ⟨other, tail, dropped⟩ : ∃ other tail,
      table.entries.dropWhile (fun entry => entry.1 != key.toInt) =
        (other, [.integer key, .integer amount]) :: tail := by
    cases rest : table.entries.dropWhile (fun entry => entry.1 != key.toInt) with
    | nil => simp [rest, found] at observations
    | cons entry tail =>
      rcases entry with ⟨other, row⟩
      simp [rest, found] at observations
      subst row
      exact ⟨other, tail, rfl⟩
  unfold Shell.execute
  rw [Nat.add_comm 7 (4 * table.entries.length)]
  have offsets : List.range 2 = [0, 1] := rfl
  simp [Shell.seek, Vdbe.run, Vdbe.step, Vdbe.execute, Vdbe.State.initial,
    Vdbe.State.advance, Vdbe.State.write, Vdbe.State.setCursor, Vdbe.State.seekCursor,
    Vdbe.State.jump, Vdbe.State.emit, Vdbe.Cursor.current?, Shell.Column.name, dropped,
    offsets, run_halted]
  rfl

end Silmaril.Proofs.Formats.Sqlite.Shell.Seek

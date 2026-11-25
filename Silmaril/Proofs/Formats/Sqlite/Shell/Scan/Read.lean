module

public import Silmaril.Formats.Sqlite.Shell.Defs
public import Silmaril.Formats.Sqlite.WriteProfile.Defs

public section

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile

namespace Silmaril.Proofs.Formats.Sqlite.Shell.Scan

private def database (table : Vdbe.Table) : Vdbe.Database :=
  fun db root => if db == 0 && root == 2 then some table else none

private def positioned (table : Vdbe.Table) (remaining : List (Int × List Value))
    (registers : Nat → Value) (rows : List (List Value)) : Vdbe.State where
  pc := if remaining.isEmpty then 6 else 2
  registers := registers
  cursors := fun index =>
    if index = 0 then some ⟨table, some remaining, true⟩ else none
  rows := rows

private def rowRegisters (registers : Nat → Value) (first second : Value) : Nat → Value :=
  fun index => if index = 2 then second else if index = 1 then first else registers index

private theorem override_shadow {α : Type} {condition : Prop} [Decidable condition]
    (new old fallback : α) :
    (if condition then new else if condition then old else fallback) =
      (if condition then new else fallback) := by
  by_cases active : condition <;> simp [active]

private theorem run_halted (db : Vdbe.Database) (program : Vdbe.Program)
    (fuel : Nat) (state : Vdbe.State) (halted : state.halted.isSome = true) :
    Vdbe.run db program fuel state = .halted state := by
  cases fuel <;> simp [Vdbe.run, halted]

private theorem enter_scan (table : Vdbe.Table) (fuel : Nat) :
    Vdbe.run (database table) Shell.scan (fuel + 2) .initial =
      Vdbe.run (database table) Shell.scan fuel
        (positioned table table.entries (fun _ => .null) []) := by
  simp [database, positioned, Shell.scan, Vdbe.run, Vdbe.step, Vdbe.execute,
    Vdbe.State.initial, Vdbe.State.advance, Vdbe.State.setCursor, Vdbe.State.rewindCursor, Vdbe.State.jump,
    override_shadow]

private theorem scan_row (table : Vdbe.Table) (key : Int) (first second : Value)
    (remaining : List (Int × List Value)) (registers : Nat → Value) (rows : List (List Value))
    (fuel : Nat) :
    Vdbe.run (database table) Shell.scan (fuel + 4)
        (positioned table ((key, [first, second]) :: remaining) registers rows) =
      Vdbe.run (database table) Shell.scan fuel
        (positioned table remaining (rowRegisters registers first second) (rows ++ [[first, second]])) := by
  have offsets : List.range 2 = [0, 1] := rfl
  simp [positioned, Shell.scan, Vdbe.run, Vdbe.step, Vdbe.execute,
    Vdbe.State.advance, Vdbe.State.write, Vdbe.State.setCursor, Vdbe.State.nextCursor, Vdbe.State.jump,
    Vdbe.State.emit, Vdbe.Cursor.current?, offsets, override_shadow]
  rfl

private theorem scan_end (table : Vdbe.Table) (registers : Nat → Value) (rows : List (List Value))
    (fuel : Nat) :
    Vdbe.run (database table) Shell.scan (fuel + 1) (positioned table [] registers rows) =
      .halted { positioned table [] registers rows with halted := some 0 } := by
  simp [positioned, Shell.scan, Vdbe.run, Vdbe.step, Vdbe.execute, run_halted]

private theorem scan_remaining (table : Vdbe.Table) (remaining : List (Int × List Value))
    (shape : ∀ entry ∈ remaining, ∃ first second, entry.2 = [first, second])
    (registers : Nat → Value) (rows : List (List Value)) (fuel : Nat) :
    ∃ final, Vdbe.run (database table) Shell.scan (fuel + 4 * remaining.length + 1)
          (positioned table remaining registers rows) = .halted final ∧
        final.halted = some 0 ∧ final.rows = rows ++ remaining.map Prod.snd := by
  induction remaining generalizing registers rows with
  | nil =>
    refine ⟨{ positioned table [] registers rows with halted := some 0 }, ?_, rfl, ?_⟩
    · simpa using scan_end table registers rows fuel
    · simp [positioned]
  | cons entry tail ih =>
    obtain ⟨first, second, shapeHead⟩ := shape entry (by simp)
    rcases entry with ⟨key, values⟩
    change values = [first, second] at shapeHead
    subst values
    have tailShape : ∀ item ∈ tail, ∃ first second, item.2 = [first, second] := by
      intro item member
      exact shape item (by simp [member])
    have count : fuel + 4 * ((key, [first, second]) :: tail).length + 1 =
        (fuel + 4 * tail.length + 1) + 4 := by simp; omega
    rw [count, scan_row]
    obtain ⟨final, run, halted, emitted⟩ :=
      ih tailShape (rowRegisters registers first second) (rows ++ [[first, second]])
    refine ⟨final, run, halted, ?_⟩
    simpa [List.append_assoc] using emitted

private theorem render_rows (rows : List Row) :
    ((rows.map Row.entry).map Prod.snd).mapM (fun row =>
      match row with
      | [.integer id, .integer amount] => (pure [id.toInt, amount.toInt] : Except String (List Int))
      | _ => throw "unexpected VM row") =
      .ok (rows.map fun row => [row.id.toInt, row.amount.toInt]) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, List.mapM_cons, Row.entry]
    rw [ih]
    rfl

/-- The default two-column scan runs the existing VM program to completion
and returns exactly the ordered rows of the supported snapshot. -/
theorem execute_scan (snapshot : Snapshot) :
    Shell.execute snapshot.readTable { columns := [.id, .amount] } =
      .ok ⟨["id", "amount"], snapshot.orderedRows.map fun row => [row.id.toInt, row.amount.toInt]⟩ := by
  let table := snapshot.readTable
  have entries : table.entries = snapshot.orderedRows.map Row.entry := rfl
  have shape : ∀ entry ∈ table.entries, ∃ first second, entry.2 = [first, second] := by
    intro entry member
    rw [entries] at member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    exact ⟨_, _, rfl⟩
  obtain ⟨final, run, halted, emitted⟩ := scan_remaining table table.entries shape (fun _ => .null) [] 4
  have programRun : Vdbe.run (fun db root => if db == 0 && root == 2 then some table else none)
      Shell.scan (7 + 4 * table.entries.length) .initial = .halted final := by
    have fuel : 7 + 4 * table.entries.length = (4 + 4 * table.entries.length + 1) + 2 := by omega
    change Vdbe.run (database table) Shell.scan (7 + 4 * table.entries.length) .initial = _
    rw [fuel, enter_scan]
    exact run
  simp at programRun
  change Shell.execute table { columns := [.id, .amount] } = _
  simp [Shell.execute, programRun, halted, Shell.Column.name]
  rw [emitted, entries, List.nil_append]
  exact render_rows snapshot.orderedRows

end Silmaril.Proofs.Formats.Sqlite.Shell.Scan

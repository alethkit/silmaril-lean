module

public import Silmaril.Formats.Sqlite.Record.Defs
import Silmaril.Formats.Sqlite.File.Thms

public section

namespace Silmaril.Proofs.Formats.Sqlite.Record.Layout

open Silmaril.Formats.Sqlite Silmaril.Formats.Sqlite.Record

theorem columnsAux?_layout (source : File.View) (codes : List Nat) (offset : Nat)
    (inside : offset ≤ source.length) {columns : List Column} {next : Nat}
    (read : columnsAux? source codes offset = some (columns, next)) :
    columns.map Column.code = codes ∧
    next = offset + (codes.map fun code => (serialType code).width).sum ∧
    next ≤ source.length ∧
    ∀ slot column, columns[slot]? = some column →
      column.payload.source = source.source ∧
      column.payload.start = source.start + offset +
        ((codes.take slot).map fun code => (serialType code).width).sum ∧
      column.payload.length = (serialType column.code).width := by
  induction codes generalizing offset columns next with
  | nil =>
    cases read
    exact ⟨rfl, by simp, inside, by simp⟩
  | cons code codes ih =>
    simp only [columnsAux?] at read
    split at read
    · cases read
    · obtain ⟨payload, subview, read⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨⟨rest, stop⟩, tail, read⟩ := Option.bind_eq_some_iff.mp read
      have extent := File.View.sub?_spec source payload offset (serialType code).width subview
      obtain ⟨codeOrder, stopAt, bounded, layout⟩ := ih _ extent.2.2.2 tail
      cases read
      refine ⟨by simp [codeOrder], ?_, bounded, ?_⟩
      · simpa [Nat.add_assoc] using stopAt
      · intro slot column lookup
        cases slot with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
          subst column
          simpa using And.intro extent.1 (And.intro extent.2.1 extent.2.2.1)
        | succ slot =>
          simp only [List.getElem?_cons_succ] at lookup
          obtain ⟨same, start, length⟩ := layout slot column lookup
          exact ⟨same, by simpa [Nat.add_assoc] using start, length⟩

theorem columnsAux?_truncated (source : File.View) (codes : List Nat) (offset : Nat)
    (inside : offset ≤ source.length)
    (overrun : source.length < offset + (codes.map fun code => (serialType code).width).sum) :
    columnsAux? source codes offset = none := by
  cases read : columnsAux? source codes offset with
  | none => rfl
  | some result =>
    obtain ⟨columns, next⟩ := result
    have result := columnsAux?_layout source codes offset inside read
    omega

theorem parse?_layout {source : File.View} {record : Parsed}
    (parsed : parse? source = some record) :
    record.source = source ∧
    record.headerSize +
      (record.columns.toList.map fun column => (serialType column.code).width).sum = source.length ∧
    ∀ slot column, record.columns.toList[slot]? = some column →
      column.payload.source = source.source ∧
      column.payload.start = source.start + record.headerSize +
        ((record.columns.toList.take slot).map fun column => (serialType column.code).width).sum ∧
      column.payload.length = (serialType column.code).width := by
  unfold parse? at parsed
  obtain ⟨⟨size, first⟩, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  dsimp only at parsed
  split at parsed
  · cases parsed
  · rename_i admitted
    have inside : size ≤ source.length := by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at admitted
      omega
    obtain ⟨codes, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
    obtain ⟨⟨columns, next⟩, read, parsed⟩ := Option.bind_eq_some_iff.mp parsed
    dsimp only at parsed
    split at parsed
    · cases parsed
    · rename_i exhausted
      have endOfView : next = source.length := by simpa using exhausted
      obtain ⟨codeOrder, exactEnd, _, layout⟩ := columnsAux?_layout source codes size inside read
      cases parsed
      subst codes
      refine ⟨rfl, ?_, ?_⟩
      · simpa [List.map_map, Function.comp_def] using exactEnd.symm.trans endOfView
      · intro slot column found
        simpa [List.map_map, Function.comp_def] using
          layout slot column (by simpa using found)

end Silmaril.Proofs.Formats.Sqlite.Record.Layout

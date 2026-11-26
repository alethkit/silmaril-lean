module

public import Silmaril.Formats.Sqlite.Record.Defs
import Silmaril.Formats.Sqlite.Record.Layout.Thms

public section

namespace Silmaril.Proofs.Formats.Sqlite.Record.Admission

open Silmaril.Formats.Sqlite Silmaril.Formats.Sqlite.Record

private theorem columnsAux?_cons_of_kind (source : File.View) (code : Nat) (codes : List Nat)
    (offset : Nat) (allowed : ∀ tag, serialType code ≠ .reserved tag) :
    columnsAux? source (code :: codes) offset = (do
      let width := (serialType code).width
      let payload ← source.sub? offset width
      let (rest, next) ← columnsAux? source codes (offset + width)
      pure (⟨code, payload⟩ :: rest, next)) := by
  cases kind : serialType code <;> simp [columnsAux?, kind]
  exact False.elim (allowed _ kind)

private theorem columnsAux?_allowed (source : File.View) (codes : List Nat) (offset : Nat)
    {columns : List Column} {next : Nat} (read : columnsAux? source codes offset = some (columns, next)) :
    ∀ code ∈ codes, ∀ tag, serialType code ≠ .reserved tag := by
  induction codes generalizing offset columns next with
  | nil => simp
  | cons head tail ih =>
    have allowed : ∀ tag, serialType head ≠ .reserved tag := by
      intro tag reserved
      simp [columnsAux?, reserved] at read
    rw [columnsAux?_cons_of_kind source head tail offset allowed] at read
    dsimp only at read
    obtain ⟨payload, _, read⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨⟨rest, stop⟩, further, _⟩ := Option.bind_eq_some_iff.mp read
    intro code member
    rcases List.mem_cons.mp member with rfl | inTail
    · exact allowed
    · exact ih _ further _ inTail

private theorem columnsAux?_fits (source : File.View) (codes : List Nat) (offset : Nat)
    (allowed : ∀ code ∈ codes, ∀ tag, serialType code ≠ .reserved tag)
    (fit : offset + (codes.map fun code => (serialType code).width).sum ≤ source.length) :
    ∃ columns, columnsAux? source codes offset =
      some (columns, offset + (codes.map fun code => (serialType code).width).sum) := by
  induction codes generalizing offset with
  | nil => exact ⟨[], by simp [columnsAux?]⟩
  | cons head tail ih =>
    have headAllowed : ∀ tag, serialType head ≠ .reserved tag := allowed head (by simp)
    simp only [List.map_cons, List.sum_cons, ← Nat.add_assoc] at fit ⊢
    have bound : offset + (serialType head).width ≤ source.length := by omega
    let payload : File.View :=
      ⟨source.source, source.start + offset, (serialType head).width, by
        have := source.bounded
        omega⟩
    have view : source.sub? offset (serialType head).width = some payload := by
      simp [File.View.sub?, bound, payload]
    obtain ⟨rest, further⟩ := ih _ (fun code member => allowed code (by simp [member])) fit
    exact ⟨⟨head, payload⟩ :: rest, by
      rw [columnsAux?_cons_of_kind source head tail offset headAllowed]
      simp [view, further]⟩

theorem columnsAux?_admission (source : File.View) (codes : List Nat) (offset : Nat)
    (inside : offset ≤ source.length) :
    (∃ columns next, columnsAux? source codes offset = some (columns, next)) ↔
    (∀ code ∈ codes, ∀ tag, serialType code ≠ .reserved tag) ∧
      offset + (codes.map fun code => (serialType code).width).sum ≤ source.length := by
  constructor
  · rintro ⟨columns, next, read⟩
    obtain ⟨_, stop, bounded, _⟩ := columnsAux?_layout source codes offset inside read
    exact ⟨columnsAux?_allowed source codes offset read, stop ▸ bounded⟩
  · rintro ⟨allowed, fit⟩
    obtain ⟨columns, read⟩ := columnsAux?_fits source codes offset allowed fit
    exact ⟨columns, _, read⟩

theorem parse?_admission (source : File.View) :
    (∃ record, parse? source = some record) ↔
    ∃ size first codes,
      Varint.readNat? source 0 = some (size, first) ∧
      first ≤ size ∧ size ≤ source.length ∧
      headerAux? source size size first = some codes ∧
      (∀ code ∈ codes, ∀ tag, serialType code ≠ .reserved tag) ∧
      size + (codes.map fun code => (serialType code).width).sum = source.length := by
  constructor
  · rintro ⟨record, parsed⟩
    unfold parse? at parsed
    obtain ⟨⟨size, first⟩, head, parsed⟩ := Option.bind_eq_some_iff.mp parsed
    dsimp only at parsed
    split at parsed
    · cases parsed
    · rename_i admitted
      simp only [Bool.or_eq_true, decide_eq_true_eq] at admitted
      have lower : first ≤ size := by omega
      have upper : size ≤ source.length := by omega
      obtain ⟨codes, header, parsed⟩ := Option.bind_eq_some_iff.mp parsed
      obtain ⟨⟨columns, next⟩, read, parsed⟩ := Option.bind_eq_some_iff.mp parsed
      dsimp only at parsed
      split at parsed
      · cases parsed
      · rename_i exhausted
        have endOfView : next = source.length := by simpa using exhausted
        have exactEnd := (columnsAux?_layout source codes size upper read).2.1
        exact ⟨size, first, codes, head, lower, upper, header,
          columnsAux?_allowed source codes size read, exactEnd.symm.trans endOfView⟩
  · rintro ⟨size, first, codes, head, lower, upper, header, allowed, exactEnd⟩
    obtain ⟨columns, read⟩ := columnsAux?_fits source codes size allowed (Nat.le_of_eq exactEnd)
    rw [exactEnd] at read
    exact ⟨⟨source, size, columns.toArray⟩, by
      simp [parse?, head, Nat.not_lt_of_ge lower, Nat.not_lt_of_ge upper, header, read]⟩

end Silmaril.Proofs.Formats.Sqlite.Record.Admission

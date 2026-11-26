module

import Silmaril.Relational.Table.Thms

namespace Silmaril.Relational.Examples

private def Cell : Bool → Type
  | false => Nat
  | true => Bool

private def sample : Row (fun c : Bool => c) Cell
  | false => (7 : Nat)
  | true => true

private def next : Row (fun c : Bool => c) Cell
  | false => (8 : Nat)
  | true => false

example : (AlignedColumns.ofRows [sample, next, sample]).values false = ([7, 8, 7] : List Nat) := rfl
example : (AlignedColumns.ofRows [sample, next, sample]).values true = [true, false, true] := rfl
example : (AlignedColumns.ofRows [sample, next, sample]).toRows = [sample, next, sample] := by simp

example : (rowsEquivColumns (RowId := Fin 2) (Fin.cases sample (fun _ => next))) true 1 = false := rfl

private def emptyRow : Row (fun _ : Fin 0 => false) Cell := Fin.elim0

example : (AlignedColumns.ofRows [emptyRow, emptyRow]).rowCount = 2 := rfl
example : (AlignedColumns.ofRows [emptyRow, emptyRow]).toRows = [emptyRow, emptyRow] := by simp

open CategoryTheory

private def named : NamedSchema (Fin 2) Unit :=
  ⟨fun _ => True, fun _ => ()⟩

private def forward : NamedPositionalSchema (Fin 2) Unit where
  named := named
  width := 2
  column := ⟨fun i => ⟨i, trivial⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩

private def backward : NamedPositionalSchema (Fin 2) Unit where
  named := named
  width := 2
  column := ⟨fun i => ⟨i.rev, trivial⟩, fun i => i.val.rev,
    Fin.rev_rev, fun i => Subtype.ext (Fin.rev_rev i.val)⟩

private def swapPositions : forward ⟶ backward := ColumnMap.id named.label

example : (NamedPositionalSchema.positionMap swapPositions).index (0 : Fin 2) = (1 : Fin 2) := rfl

private def unitKind (_ : Unit) := ()
private abbrev natCell (_ : Unit) := Nat

private def doubled : GeneratedColumns unitKind unitKind natCell where
  Dependency _ := Unit
  input _ _ := ()
  eval _ input := 2 * input ()

private instance (candidate : GeneratedColumns.Candidate unitKind unitKind natCell) :
    Decidable (doubled.Valid candidate) :=
  decidable_of_iff (candidate.2 () = doubled.evaluate candidate.1 ())
    ⟨fun h () => h, fun h => h ()⟩

example : (doubled.reconstruct (fun _ => 3)).val.2 () = 6 := rfl
example : (doubled.check (fun _ => 3, fun _ => 6)).isSome = true := by decide
example : doubled.check (fun _ => 3, fun _ => 5) = none := by decide

end Silmaril.Relational.Examples

module
public import Silmaril.Formats.Sqlite.File.Defs
import Silmaril.Proofs.Formats.Sqlite.File

public section
namespace Silmaril.Formats.Sqlite.File

@[simp] theorem View.get?_outOfBounds (view : View) (offset : Nat) (h : view.length ≤ offset) :
    view.get? offset = none := by simp [View.get?, Nat.not_lt_of_ge h]

theorem View.sub?_spec (view part : View) (offset count : Nat)
    (h : view.sub? offset count = some part) :
    part.source = view.source ∧ part.start = view.start + offset ∧
      part.length = count ∧ offset + count ≤ view.length :=
  Silmaril.Proofs.Formats.Sqlite.File.View.sub?_spec view part offset count h

theorem View.sub?_read (view part : View) (offset count index : Nat)
    (h : view.sub? offset count = some part) (inside : index < count) :
    part.get? index = view.get? (offset + index) := by
  obtain ⟨source,start,length,bounded⟩ := View.sub?_spec view part offset count h
  simp only [View.get?, length, inside, ↓reduceIte, source, start]
  rw [ite_eq_left (by omega : offset + index < view.length), Nat.add_assoc]

theorem Image.page?_spec (image : Image) (number : Nat) (view : View)
    (h : image.page? number = some view) :
    0 < number ∧ number ≤ image.pageCount ∧ view.source = image.source ∧
      view.start = (number-1)*image.header.pageSize ∧ view.length = image.header.pageSize :=
  Silmaril.Proofs.Formats.Sqlite.File.Image.page?_spec image number view h

theorem Image.usablePage?_length (image : Image) (number : Nat) (view : View)
    (h : image.usablePage? number = some view) : view.length = image.header.usableSize :=
  Silmaril.Proofs.Formats.Sqlite.File.Image.usablePage?_length image number view h

@[simp] theorem Header.usableSize_add_reserved (header : Header)
    (bounded : header.reserved ≤ header.pageSize) :
    header.usableSize + header.reserved = header.pageSize := by
  simp only [Header.usableSize]
  omega

@[simp] theorem pointerMapPage_two (header : Header) (lock : header.lockPage ≠ 2) :
    pointerMapPage header 2 = 2 := by simp [pointerMapPage, Ne.symm lock]

end Silmaril.Formats.Sqlite.File

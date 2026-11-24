module

public import Silmaril.Formats.Sqlite.File.Defs

public section

namespace Silmaril.Proofs.Formats.Sqlite.File

open Silmaril.Formats Silmaril.Formats.Sqlite Silmaril.Formats.Sqlite.File
open Silmaril.Formats.Sqlite.File.View

theorem View.sub?_spec (view part : View) (offset count : Nat)
    (h : view.sub? offset count = some part) :
    part.source = view.source ∧ part.start = view.start + offset ∧
      part.length = count ∧ offset + count ≤ view.length := by
  unfold sub? at h
  split at h
  next bounded => cases h; exact ⟨rfl,rfl,rfl,bounded⟩
  next => cases h

theorem Image.page?_spec (image : Image) (number : Nat) (view : View)
    (h : image.page? number = some view) :
    0 < number ∧ number ≤ image.pageCount ∧ view.source = image.source ∧
      view.start = (number-1)*image.header.pageSize ∧ view.length = image.header.pageSize := by
  unfold Image.page? at h
  split at h
  next => cases h
  next valid =>
    obtain ⟨source,start,length,_⟩ := View.sub?_spec _ _ _ _ h
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at valid
    exact ⟨by omega, by omega, source, by simpa [View.ofBytes] using start, length⟩

theorem Image.usablePage?_length (image : Image) (number : Nat) (view : View)
    (h : image.usablePage? number = some view) : view.length = image.header.usableSize := by
  unfold Image.usablePage? at h
  cases hp : image.page? number with
  | none => simp [hp] at h
  | some page =>
    simp only [hp] at h
    exact (View.sub?_spec page view 0 image.header.usableSize h).2.2.1

end Silmaril.Proofs.Formats.Sqlite.File

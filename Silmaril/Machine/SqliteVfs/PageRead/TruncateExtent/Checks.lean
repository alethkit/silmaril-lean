module

import Silmaril.Machine.SqliteVfs.PageRead.TruncateExtent.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.TruncateExtent

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)

private def one : FileState := ⟨[10], some .readWrite, 0⟩
private def two : FileState := ⟨[10, 0], some .readWrite, 0⟩
private def first : Page := ⟨⟨0⟩, 1, 2⟩
private def later : Page := ⟨⟨0⟩, 2, 2⟩

example : ¬ AgreesOnPage one two first := by
  intro agrees
  have count := (truncate_agrees_iff first
    (show readWrite 8 one (.truncate ⟨0⟩ 2) = (.ok (), two) from rfl)).mp agrees
  change 1 = 2 at count
  nomatch count

example : AgreesOnPage one two later :=
  (truncate_agrees_iff later
    (show readWrite 8 one (.truncate ⟨0⟩ 2) = (.ok (), two) from rfl)).mpr rfl

example : ¬ AgreesOnPage two one first := by
  intro agrees
  have count := (truncate_agrees_iff first
    (show readWrite 8 two (.truncate ⟨0⟩ 1) = (.ok (), one) from rfl)).mp agrees
  change 2 = 1 at count
  nomatch count

example : AgreesOnPage two one later :=
  (truncate_agrees_iff later
    (show readWrite 8 two (.truncate ⟨0⟩ 1) = (.ok (), one) from rfl)).mpr rfl

#print axioms truncate_agrees_iff

end Silmaril.Machine.SqliteVfs.PageRead.TruncateExtent

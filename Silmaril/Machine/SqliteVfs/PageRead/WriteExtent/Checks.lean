module

import Silmaril.Machine.SqliteVfs.PageRead.WriteExtent.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.WriteExtent

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.CacheHit (AgreesOnPage)

private def before : FileState := ⟨[10], some .readWrite, 0⟩
private def after : FileState := ⟨[10, 0, 99], some .readWrite, 0⟩
private def headPage : Page := ⟨⟨0⟩, 1, 2⟩
private def laterPage : Page := ⟨⟨0⟩, 3, 2⟩

example : ¬ AgreesOnPage before after headPage := by
  intro agrees
  have same := (disjoint_write_agrees_iff headPage
    (show readWrite 8 before (.write ⟨0⟩ 2 [99]) = (.ok (), after) from rfl)
    (.inl (by decide))).mp agrees
  change 1 = 2 at same
  nomatch same

example : AgreesOnPage before after laterPage :=
  (disjoint_write_agrees_iff laterPage
    (show readWrite 8 before (.write ⟨0⟩ 2 [99]) = (.ok (), after) from rfl)
    (.inr (by decide))).mpr rfl

#print axioms presentCount_eq_of_agreement
#print axioms disjoint_write_agrees_iff

end Silmaril.Machine.SqliteVfs.PageRead.WriteExtent

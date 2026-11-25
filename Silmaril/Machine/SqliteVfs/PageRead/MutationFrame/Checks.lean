module

import Silmaril.Machine.SqliteVfs.PageRead.MutationFrame.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.MutationFrame

open CacheHit (AgreesOnPage)

private def file : FileState := ⟨[10, 20, 30, 40, 50], some .readWrite, 0⟩
private def page : Page := ⟨⟨0⟩, 2, 2⟩

-- A write ending exactly at the page start.
private def beforePage : FileState := {file with bytes := [10, 99, 30, 40, 50]}

example : AgreesOnPage file beforePage page :=
  (write_preserves_page page (rfl : readWrite 8 file (.write page.handle 1 [99]) = (.ok (), beforePage))
    (by decide) (Or.inr (by decide))).1

-- A write beyond the original EOF creates a gap while keeping the page.
private def pastEOF : FileState := {file with bytes := [10, 20, 30, 40, 50, 0, 0, 99]}

example : AgreesOnPage file pastEOF page :=
  (write_preserves_page page (rfl : readWrite 8 file (.write page.handle 7 [99]) = (.ok (), pastEOF))
    (by decide) (Or.inl (by decide))).1

-- A truncate to the exclusive page endpoint keeps the full page.
private def truncated : FileState := {file with bytes := [10, 20, 30, 40]}

example : AgreesOnPage file truncated page :=
  (truncate_preserves_page page (rfl : readWrite 8 file (.truncate page.handle 4) = (.ok (), truncated))
    (by decide) (by decide)).1

private def overwritten : FileState := {file with bytes := [10, 20, 99, 40, 50]}

example : readWrite 8 file (.write page.handle 2 [99]) = (.ok (), overwritten) ∧
    ¬ AgreesOnPage file overwritten page := by
  refine ⟨rfl, fun agrees => ?_⟩
  have first := agrees 0 (by decide)
  change some (30 : UInt8) = some 99 at first
  nomatch first

#print axioms write_preserves_page
#print axioms truncate_preserves_page

end Silmaril.Machine.SqliteVfs.PageRead.MutationFrame

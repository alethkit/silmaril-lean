module

import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.Acquire

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def file : FileState := ⟨[10, 20, 30, 40], some .readOnly, 0⟩
private def page : Page := ⟨⟨0⟩, 2, 2⟩
private def cache : Cache := fun slot => if slot = 3 then some .vacant else none

example :
    let cold := acquire (readOnly 8) file cache 3 page
    let warm := acquire (readOnly 8) cold.file cold.cache 3 page
    warm.result = .ok [30, 40] ∧
      warm.cache 3 = some (.resident page [30, 40]) ∧
      cold.trace ++ warm.trace = [⟨page.request, .ok [30, 40]⟩] := by
  have checked := readOnly_cold_warm 8 file cache 3 page rfl (by decide) rfl (by decide)
  dsimp only at checked ⊢
  rw [checked.2.1, checked.1]
  exact ⟨rfl, rfl, rfl⟩

example :
    let occupied := cache.install 3 page [30, 40]
    let other : Page := ⟨⟨1⟩, 2, 2⟩
    let after := acquire (readOnly 8) file occupied 3 other
    after.result = .error .unavailableSlot ∧ after.cache = occupied ∧ after.trace = [] :=
  ⟨rfl, rfl, rfl⟩

#print axioms acquire_hit
#print axioms acquire_miss
#print axioms acquire_trace
#print axioms readOnly_cold_warm

end Silmaril.Machine.SqliteVfs.PageRead.Acquire

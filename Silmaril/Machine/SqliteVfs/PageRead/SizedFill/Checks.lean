module

import Silmaril.Machine.SqliteVfs.PageRead.SizedFill.Thms
import Silmaril.Machine.SqliteVfs.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.SizedFill

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def counting : Handler (FileState × Nat) := fun state request =>
  let result := readOnly 4 state.1 request
  (result.1, (result.2, state.2 + 1))

private theorem countingLaw : ReadLaw counting Prod.fst where
  read state handle offset count := by
    have rule := (readOnly_lawful 4).2.1.read state.1 handle offset count
    simpa [counting] using rule
  fileSize state handle := by
    have rule := (readOnly_lawful 4).2.1.fileSize state.1 handle
    simpa [counting] using rule

private def initial : FileState × Nat := (⟨[10, 20, 30, 40], some .readOnly, 0⟩, 0)
private def page : Page := ⟨⟨0⟩, 2, 2⟩
private def cache : Cache := fun slot => if slot = 0 then some .vacant else none

example :
    let sized := (counting initial (.fileSize page.handle)).2
    let outcome := fill counting sized cache 0 page
    outcome.result = .ok [30, 40] ∧ outcome.file.2 = 2 ∧
      Trace.Valid counting initial [⟨.fileSize page.handle, .ok 4⟩,
        ⟨page.request, .ok [30, 40]⟩] outcome.file := by
  have checked := size_then_full_fill countingLaw initial cache 0 page 4 rfl
    (by decide) rfl (by decide)
  exact ⟨rfl, rfl, checked.2.2.2⟩

example :
    let small : FileState × Nat := (⟨[10, 20, 30], some .readOnly, 0⟩, 0)
    let sized := counting small (.fileSize page.handle)
    sized.1 = .ok 3 ∧ ¬ page.offset + page.size ≤ 3 ∧
      (fill counting sized.2 cache 0 page).result = .error .shortRead :=
  ⟨rfl, by decide, rfl⟩

#print axioms size_then_full_fill
#print axioms countingLaw

end Silmaril.Machine.SqliteVfs.PageRead.SizedFill

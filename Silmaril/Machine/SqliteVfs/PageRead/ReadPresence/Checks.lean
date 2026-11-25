module

import Silmaril.Machine.SqliteVfs.PageRead.ReadPresence.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.ReadPresence

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def page : Page := ⟨⟨0⟩, 1, 3⟩
private def before : FileState := ⟨[10], some .readOnly, 0⟩
private def after : FileState := ⟨[10, 0], some .readOnly, 0⟩

example :
    (readOnly 3 before page.request).1 = .shortRead [10, 0, 0] ∧
    (readOnly 3 after page.request).1 = .shortRead [10, 0, 0] ∧
    WriteExtent.presentCount before page = 1 ∧ WriteExtent.presentCount after page = 2 ∧
    ¬ CacheHit.AgreesOnPage before after page := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro agrees
  have differs := agrees 1 (by decide)
  change none = some (0 : UInt8) at differs
  contradiction

#print axioms read_result_agreement_iff

end Silmaril.Machine.SqliteVfs.PageRead.ReadPresence

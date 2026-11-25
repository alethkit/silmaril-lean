module

import Silmaril.Machine.SqliteVfs.PageRead.Reopen.Thms
import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs
import Silmaril.Machine.SqliteVfs.Thms

namespace Silmaril.Machine.SqliteVfs.PageRead.Reopen

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

private def file : FileState := ⟨[10, 20, 30, 40], some .readOnly, 7⟩
private def oldPage : Page := ⟨⟨7⟩, 2, 2⟩
private def newPage : Page := ⟨⟨8⟩, 2, 2⟩
private def cache : Cache := fun slot =>
  if slot = 0 then some .vacant else if slot = 1 then some (.resident oldPage [30, 40]) else none

example :
    let closed := (readOnly 4 file (.close oldPage.handle)).2
    let opened := (readOnly 4 closed (.openFile .readOnly)).2
    let stale := fill (readOnly 4) opened cache 0 oldPage
    Trace.Valid (readOnly 4) file
      [⟨.close oldPage.handle, .ok ()⟩, ⟨.openFile .readOnly, .ok newPage.handle⟩,
        ⟨oldPage.request, .error .invalidHandle⟩] stale.file ∧
      stale.cache 1 = some (.resident oldPage [30, 40]) ∧
      CacheHit.lookup stale.cache 1 newPage = none ∧
      (fill (readOnly 4) stale.file stale.cache 0 newPage).result = .ok [30, 40] := by
  have law := readOnly_lawful 4
  have stale := stale_fill_after_reopen law.1 law.2.1 file cache 0 oldPage rfl rfl (by decide)
  exact ⟨stale.2.2, rfl, rfl, rfl⟩

#print axioms stale_fill_after_reopen

end Silmaril.Machine.SqliteVfs.PageRead.Reopen

module

public import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.Acquire

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- A matching resident supplies its stored bytes. Other cases retain the
ordinary fill rules, including refusal to replace an occupied slot.
The caller accounts for freshness of resident bytes. -/
def acquire {State : Type} (handler : Handler State) (file : State) (cache : Cache)
    (target : SlotId) (page : Page) : Outcome State :=
  match CacheHit.lookup cache target page with
  | some bytes => ⟨.ok bytes, file, cache, []⟩
  | none => fill handler file cache target page

end Silmaril.Machine.SqliteVfs.PageRead.Acquire

module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs
public import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.CacheHit

open Silmaril.Formats.Sqlite

/-- The selected slot must contain exactly this handle, page number and size. -/
def lookup (cache : Cache) (target : SlotId) (page : Page) : Option Bytes :=
  match cache target with
  | some (.resident stored bytes) => if stored = page then some bytes else none
  | _ => none

/-- Only the requested interval must agree between the two snapshots. -/
def AgreesOnPage (before current : FileState) (page : Page) : Prop :=
  ∀ i, i < page.size → before.bytes[page.offset + i]? = current.bytes[page.offset + i]?

/-- The outer layer indicates a page was supplied. The inner layer retains
leaf or row rejection separately from every completed VDBE outcome. -/
def runPage? (bytes : Option Bytes) (base db root : Nat) (program : Vdbe.Program)
    (fuel : Nat) (initial : Vdbe.State) : Option (Option Vdbe.RunResult) :=
  bytes.map fun data =>
    FileView.VdbeLeaf.run? (File.View.ofBytes (Silmaril.Formats.Bytes.ofList data))
      base db root program fuel initial

/-- A pure cache lookup and VM observation. There are no VFS events. -/
def runHit? (cache : Cache) (target : SlotId) (page : Page) (base db root : Nat)
    (program : Vdbe.Program) (fuel : Nat) (initial : Vdbe.State) : Option (Option Vdbe.RunResult) :=
  runPage? (lookup cache target page) base db root program fuel initial

end Silmaril.Machine.SqliteVfs.PageRead.CacheHit

module

public import Silmaril.Containers.SqliteVfs.ReadReturn.Defs
public import Silmaril.Elf.Corpus.SqliteRead.Defs
import Silmaril.Proofs.Containers.SqliteVfs.ReadReturn.NativeEntry.Compose

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.ReadReturn.NativeEntry

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs
open Silmaril.Containers.SqliteVfs.ReadEntry (projectEntry)
open Silmaril.Containers.SqliteVfs.ReadReturn (projectReturn)
open Silmaril.Elf.Corpus.SqliteRead (Dispatches argument observe run)
open Silmaril.Machine
open Silmaril.Machine.Behaviour.Observable (Safe)
open Silmaril.Machine.SqliteRead (BufferView Status)
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary
open Silmaril.X86 (MState Word)
open Silmaril.X86.Ext.Wire (Platform)

/-- The actual pinned entry supplies the ABI request to the modeled return.
The pre/post buffer views and handler law are supplied as premises. -/
theorem pinned_entry_with_modeled_return (capacity : Nat) (file : FileState)
    (cache : Cache) (slot : SlotId) {platform : Platform} {initial : MState}
    {elfPage : Silmaril.Elf.Corpus.SqliteRead.PageRead} {methods target : Word}
    {env : SqliteRead.Context} {binding : FileBinding} (page : Page)
    (entry : Silmaril.Elf.Corpus.SqliteRead.Entry initial elfPage methods target)
    (safe : Safe ((SqliteRead.contract env).spec elfPage.request))
    (bound : binding elfPage.file = some page.handle)
    (number : page.number = elfPage.index + 1) (size : page.size = elfPage.count.toNat)
    (live : (file.mode page.handle).isNone = false) (owned : cache slot = some .vacant)
    (before after : BufferView) (status : Status)
    (law : SqliteRead.Handler (file.bytes.map UInt8.toBitVec) elfPage.request before after status)
    (supported : status = .ok ∨ status = .shortRead) :
    let outcome := fill (readOnly capacity) file cache slot page
    ∃ entryState exchange,
      Dispatches platform initial elfPage.request target entryState ∧
      projectEntry binding (observe (run platform 3 initial)) = some (.recv exchange.request) ∧
      projectReturn binding (argument entryState.core) after status = some exchange ∧
      (machine (readOnly capacity)).Exec Mach.seqPolicy (.idle file) [.recv exchange.request]
        (.pending file exchange.request) ∧
      outcome.trace = [exchange] ∧
      (machine (readOnly capacity)).Exec Mach.seqPolicy (.idle file) (encode [exchange])
        (.idle outcome.file) :=
  Proofs.Containers.SqliteVfs.ReadReturn.NativeEntry.pinned_entry_with_modeled_return capacity
    file cache slot page entry safe bound number size live owned before after status law supported

end Silmaril.Containers.SqliteVfs.ReadReturn.NativeEntry

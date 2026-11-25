module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control

open Silmaril.X86.Concurrency.Sqlite
open Silmaril.X86.MemoryModel.Tso hiding Execution

/-- The seven memory accesses before the exchange and the exchange cover exactly
the five consecutive mutex dwords and the private-threading flag byte. -/
theorem issued_bytes (tid base : Nat) (users kind : BitVec 32) :
    issuedBytes (FifoData.dataEvents tid base users kind) = footprint base :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.issued_bytes tid base users kind

/-- Every confined FIFO run of the selected data labels matches one abstract
control release and stays within the declared issued footprint. The confinement
covers pending writes through the last silent flush. -/
theorem confined_sound (tid base : Nat) (busy rc : Int32) (users kind : BitVec 32) :
    Sound .fifo id (fun _ run => run.labels = FifoData.dataEvents tid base users kind)
      (projection tid base busy) (fun _ _ => footprint base)
      (confined tid base busy rc) :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control.confined_sound
    tid base busy rc users kind

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Control

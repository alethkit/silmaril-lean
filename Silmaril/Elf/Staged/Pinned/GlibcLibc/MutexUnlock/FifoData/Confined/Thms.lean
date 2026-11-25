module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Defs
public import Silmaril.X86.Concurrency.Sqlite.Release.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Confined

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Confined

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock
open Silmaril.X86.MemoryModel.Tso hiding Execution
open Silmaril.X86.MemoryModel
open Silmaril.X86.Concurrency.Sqlite.Release (PeerBuffersAvoid)

/-- At a byte omitted by every initially pending peer store, all executions
of the eight data labels agree with the issuer's initial forwarded value
updated by the four issued writes. The exchange drains the issuer. -/
theorem release_byte {initial final : XState Nat} {tid base address : Nat}
    {users kind : BitVec 32}
    (path : Tso.Execution XWeakStep initial (FifoData.dataEvents tid base users kind) final)
    (safe : PeerBuffersAvoid initial tid address) :
    final.buffer tid = [] ∧
      final.memory address = writeMem (FifoData.committedStores (viewMem initial tid) base users)
        base FifoData.zeroDword address :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Confined.release_byte path safe

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Confined

module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveEntryReturn.Defs
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveEntryReturn

public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveEntryReturn

open Silmaril.X86
open Silmaril.X86.Ext (leBytes)
open Silmaril.Machine.Execution (run)
open Silmaril.Machine.LittleEndian (encodeWords)

/-- The pinned private recursive depth-one path returns zero in 37 Atomic9
steps from the mapped symbol entry. It restores the incoming RBP, pops the
caller target, and frames memory outside the saved-RBP slot and four mutex
dwords. Those two spans contain the exact saved and released bytes. -/
theorem recursive_entry_return {initial : MState} {threadId users : BitVec 32} {target : Word}
    (inputs : Entry initial threadId users target) :
    ∃ final, run Atomic9.step 37 initial = some final ∧ final.core.rip = target ∧
      final.core.read .rax = 0#64 ∧ final.core.read .rbp = initial.core.read .rbp ∧
      final.core.read .rsp = initial.core.read .rsp + 8#64 ∧
      initial.memory.WritesWithin final.memory (fun address =>
        ((savedSlot initial).toNat ≤ address ∧ address < (savedSlot initial).toNat + 8) ∨
        ((initial.core.read .rdi).toNat ≤ address ∧ address < (initial.core.read .rdi).toNat + 16)) ∧
      (∀ offset, offset < 8 → final.memory.bytes.get? ((savedSlot initial).toNat + offset) =
        (encodeWords [initial.core.read .rbp])[offset]?) ∧
      ∀ offset, offset < 4 →
        let base := (initial.core.read .rdi).toNat
        final.memory.bytes.get? (base + offset) = some 0 ∧
        final.memory.bytes.get? (base + 4 + offset) = some 0 ∧
        final.memory.bytes.get? (base + 8 + offset) = some 0 ∧
        final.memory.bytes.get? (base + 12 + offset) = (leBytes ((users - 1#32).setWidth 64) 4)[offset]? :=
  Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveEntryReturn.recursive_entry_return inputs

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.RecursiveEntryReturn

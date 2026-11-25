module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.Thms

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock

open Silmaril.Elf Silmaril.Elf.Staged.Reader
open Silmaril.X86

theorem lookup : Lookup F selector (some entry) :=
  ⟨_, parses, by decide +kernel⟩

/-- The actual exchange bytes and their inclusion in the selected symbol's extent. -/
theorem code :
    CodeAt F exchangeAddress exchangeBytes ∧
      entry.value ≤ exchangeAddress ∧ exchangeAddress + exchangeBytes.length ≤ entry.value + entry.size :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel), by decide, by decide⟩

theorem decode : Atomic9.decode exchangeBytes = some (exchange, 2) := by decide +kernel

/-- The instruction issues a locked read and write of the entire dword at RDI. -/
theorem access (s : State) :
    MemEvent.atomic9Accesses exchange s 2 = [⟨.rmw, (s.read .rdi).toNat, 4, true⟩] := by
  simp [exchange, MemEvent.atomic9Accesses, MemEvent.atomic9NewAccesses, MemEvent.rmEv,
    MemEvent.memEv, Atomic9.tag, Atomic9.RM.isMem, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Sz.bytes]

/-- A byte just above the low byte is part of the instruction's write footprint. -/
theorem writesNextByte (s : State) :
    MemEvent.writeSet (MemEvent.atomic9Accesses exchange s 2) ((s.read .rdi).toNat + 1) := by
  rw [access]
  exact ⟨_, List.mem_cons_self, rfl, Nat.le_add_right .., Nat.add_lt_add_left (show 1 < 4 by decide) _⟩

/-- A singleton low-byte footprint cannot cover this instruction. -/
theorem not_oneByte (s : State) :
    ¬ ({ addr | MemEvent.writeSet (MemEvent.atomic9Accesses exchange s 2) addr } : Set Nat) ⊆
      {(s.read .rdi).toNat} := by
  intro covered
  have impossible : (s.read .rdi).toNat + 1 = (s.read .rdi).toNat := covered (writesNextByte s)
  omega

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock

module

public import Silmaril.Elf.Facts.Defs
public import Silmaril.X86.MemEvent.Defs

/-! # The pinned glibc normal-mutex exchange site

File addresses are link-time virtual addresses in the pinned Ubuntu 2.39
`libc.so.6`. The site is inside the versioned unlock symbol. The file facts
and access list do not establish reachability from a SQLite call.
-/

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock

open Silmaril.Elf
open Silmaril.X86 (Byte)
open Silmaril.X86.Atomic9 (Instr)
open Silmaril.X86.Ext (Mem)

/-- The version requested by the pinned SQLite object's unlock relocation. -/
def selector : Sel :=
  .dyn ⟨nameOf "pthread_mutex_unlock", false, some ⟨nameOf "GLIBC_2.2.5", 157882997, false⟩⟩

def entry : Def := { index := 2690, value := 0xa1b50, size := 270, ifunc := false, abs := false }

def exchangeAddress : Nat := 0xa1ba2

def exchangeBytes : List Byte := [0x87, 0x07]

def exchange : Instr := .new (.xchg .d (.mem (Mem.ofReg .rdi none 0)) .rax)

end Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock

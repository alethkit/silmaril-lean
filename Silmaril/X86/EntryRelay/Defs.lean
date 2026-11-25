module

public import Silmaril.X86.Open.Defs

/-! A two-byte direct jump whose target is the following instruction, in the
existing open x86 model. -/

@[expose] public section
namespace Silmaril.X86.EntryRelay

/-- `jmp rel8 0`, whose target is the start of the following instruction. -/
def jumpBytes : List Byte := [0xeb, 0]

/-- Same state at the suffix entry. -/
def suffixEntry (entry : MState) : MState :=
  ⟨{ entry.core with rip := entry.core.rip + 2 }, entry.memory⟩

end Silmaril.X86.EntryRelay

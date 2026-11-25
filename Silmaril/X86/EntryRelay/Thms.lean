module

public import Silmaril.X86.EntryRelay.Defs
public import Silmaril.X86.Open.Thms
import Silmaril.Proofs.X86.EntryRelay

@[expose] public section
namespace Silmaril.X86.EntryRelay

/-- A loaded `jmp rel8 0` takes one open step, changing only RIP. -/
theorem step_to_suffix {entry : MState} {body : List Byte}
    (loaded : Ext.Loaded entry.memory entry.core.rip (jumpBytes ++ body)) :
    Open.step entry = some (suffixEntry entry) :=
  Proofs.X86.EntryRelay.step_to_suffix loaded

/-- The two entry points in the same memory have exactly the same first returns. -/
theorem firstReturn_iff_suffix {entry final : MState} {body : List Byte}
    (loaded : Ext.Loaded entry.memory entry.core.rip (jumpBytes ++ body)) :
    FnContract.FirstReturn Open.isa entry final ↔
      FnContract.FirstReturn Open.isa (suffixEntry entry) final :=
  Proofs.X86.EntryRelay.firstReturn_iff_suffix loaded

/-- A concrete state admits both the eight-byte and six-byte entry. They first
return to the same state with the version scalar in RAX and unchanged memory. -/
theorem distinct_version_witness :
    let body : List Byte := [0xb8, 0xb1, 0x99, 0x2e, 0, 0xc3]
    ∃ entry final : MState,
      Ext.Loaded entry.memory entry.core.rip (jumpBytes ++ body) ∧
      Ext.Loaded entry.memory (suffixEntry entry).core.rip body ∧
      jumpBytes ++ body ≠ body ∧
      FnContract.FirstReturn Open.isa entry final ∧
      FnContract.FirstReturn Open.isa (suffixEntry entry) final ∧
      final.core.read .rax = 3054001 ∧ final.memory = entry.memory :=
  Proofs.X86.EntryRelay.distinct_version_witness

end Silmaril.X86.EntryRelay

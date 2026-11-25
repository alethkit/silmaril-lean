module

public import Silmaril.Machine.Region.X86.SqliteStrLength.Defs
public import Silmaril.X86.Open.Thms
import Silmaril.Proofs.Machine.Region.X86.SqliteStrLength

@[expose] public section
namespace Silmaril.Machine.Region.X86.SqliteStrLength

open Silmaril.X86
open Silmaril.Process (Memory addressLimit)
open Silmaril.SSA.LambdaRTL
open Silmaril.Machine.Execution (run)

/-- The three decoded entry instructions reach the successor chosen by the CFG. -/
theorem branch_agrees {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code) :
    ∃ target branch,
      graph.entry.exec (model entry.memory) (fun label _ _ => some label) (entryStore entry) = some target ∧
      run Open.step 3 entry = some branch ∧
      branch.core.rip = entry.core.rip + branchOffset target ∧
      branch.core.read .rdi = pointer entry ∧ branch.core.read .rax = 0 ∧ branch.memory = entry.memory :=
  Proofs.Machine.Region.X86.SqliteStrLength.branch_agrees loaded

/-- Admitted entries reach their first return and agree with the graph. -/
theorem bridge_exists {entry : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (saved : ReturnSlot entry) (ready : DataReady entry) :
    ∃ final, FnContract.FirstReturn Open.isa entry final ∧ Bridge entry final :=
  Proofs.Machine.Region.X86.SqliteStrLength.bridge_exists loaded saved ready

/-- Every first return in the admitted profile matches the CFG observation. -/
theorem bridge_of_firstReturn {entry final : MState} (loaded : Ext.Loaded entry.memory entry.core.rip code)
    (saved : ReturnSlot entry) (ready : DataReady entry) (actual : FnContract.FirstReturn Open.isa entry final) :
    Bridge entry final :=
  Proofs.Machine.Region.X86.SqliteStrLength.bridge_of_firstReturn loaded saved ready actual

/-- The rule admits the null arm in a state without readable pointee bytes. -/
theorem null_witness :
    ∃ entry final, pointer entry = 0 ∧ field entry.memory 0 = none ∧
      Ext.Loaded entry.memory entry.core.rip code ∧ ReturnSlot entry ∧
      FnContract.FirstReturn Open.isa entry final ∧ Bridge entry final ∧ final.core.read .rax = 0 :=
  Proofs.Machine.Region.X86.SqliteStrLength.null_witness

/-- The rule admits a bounded non-null field containing four concrete bytes. -/
theorem bounded_witness :
    ∃ entry final, pointer entry = 0x4000 ∧ (pointer entry).toNat + 28 ≤ addressLimit ∧
      field entry.memory (pointer entry) = some 0x12345678 ∧
      Ext.Loaded entry.memory entry.core.rip code ∧ ReturnSlot entry ∧
      FnContract.FirstReturn Open.isa entry final ∧ Bridge entry final ∧ final.core.read .rax = 0x12345678 :=
  Proofs.Machine.Region.X86.SqliteStrLength.bounded_witness

end Silmaril.Machine.Region.X86.SqliteStrLength

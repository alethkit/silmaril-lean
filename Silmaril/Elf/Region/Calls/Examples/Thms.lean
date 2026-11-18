module

public import Silmaril.Elf.Region.Calls.Examples.Defs
public import Silmaril.Elf.Region.Calls.Thms
public import Silmaril.Elf.Region.Calls.Semantic.Thms
import Silmaril.Proofs.Elf.Region.CallExamples

@[expose] public section
namespace Silmaril.Elf.Region.Calls.Examples
open Silmaril.Semantics.Function

theorem direct_inventory : arcLabels inventory = [(0, 6), (6, 12)] := by decide +kernel
theorem certified_partition_count : partitionCount = some 3 := by decide +kernel
theorem hello_puts : arcLabels helloInventory = [(0x1060, 0x1050)] := by decide +kernel
theorem frontier : (query inventory 0 3).knownFrontier = [external] := by decide +kernel
theorem complete_scan : (query inventory 0 3).incomplete = false := by decide +kernel
theorem fuel_not_complete : (query inventory 0 0).incomplete = true := by decide +kernel
theorem indirect_is_open : (query indirectInventory 0 2).incomplete = true := by decide +kernel
theorem ambiguous_is_open : (query ambiguousInventory 0 2).incomplete = true := by decide +kernel
theorem unseen_opcode_is_open : (query unsupportedInventory 0 2).incomplete = true := by decide +kernel
theorem unqualified_jump_is_open : (query (tailInventory false) 0 2).incomplete = true := by decide +kernel
theorem declared_tail_arc : arcLabels (tailInventory true) = [(0, 2)] := by decide +kernel
theorem indirect_is_not_empty : (analysis indirectInventory).may ⟨⟨0, 0, .invoke⟩, .indirect,
    .foreign external⟩ :=
  ⟨none, ⟨rfl, extractRow (objectOfCode [0xff, 0xd0, 0xc3]) ⟨[⟨"indirect", 0, 3⟩], [], []⟩
    ⟨"indirect", 0, 3⟩, List.Mem.head _, List.Mem.head _⟩, trivial⟩

theorem actual_path : CallPath (mayGraph (analysis inventory).may) (.localFn 0) (.foreign external) :=
  consecutive_path Proofs.certificate.may_cover (.cons Proofs.actual_entry (.single Proofs.actual_worker))

theorem entry_body : entryBoundary.semanticBodies fixture 0 entry :=
  Proofs.certificate.body_sound ⟨rfl, rfl, rfl, rfl⟩

theorem refined_path : Consecutive refinedMachine fixture (.localFn 0) initial (.foreign external) afterWorker :=
  .cons Proofs.refined_entry (.single Proofs.refined_worker)

theorem refined_cover : CallGraphProblem (refinedMachine.actualCalls fixture) (analysis inventory) :=
  ext_covers 64 (restrict_sites Proofs.cover (fun _ _ h => h.1))

theorem refined_path_projection : CallPath (mayGraph (analysis inventory).may) (.localFn 0) (.foreign external) :=
  consecutive_path refined_cover refined_path

end Silmaril.Elf.Region.Calls.Examples

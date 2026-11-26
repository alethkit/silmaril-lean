module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.DeadStore.Search.Selection (Result storeVersions)
open Memory.DeadStore.Search.Selection.Readers renaming discover → discoverReaders
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations checked_operations)
open Discovery.MemRef.CF (Programs entryTransition run)

variable {args : List ValueSort} {cells : Nat}
variable {entry edited : Memory.Graph args}

/-- A successful edit is precisely a checked deletion of Store 1 using
Store 2 as its overwrite, with inferred reader obligations. -/
theorem rewrite_checked (input : Tuple (Val cells) args) (accepted : rewrite entry input = some edited) :
    (storeVersions entry).length = 2 ∧
      ∃ facts, discoverReaders entry 1 = some facts ∧
        Memory.DeadStore.rewrite entry ⟨1, 2⟩ facts input = some edited :=
  Proofs.rewrite_checked input accepted

theorem rewrite_denote (input : Tuple (Val cells) args) (accepted : rewrite entry input = some edited)
    (initial : Heap cells) : edited.denote input initial = entry.denote input initial :=
  Proofs.rewrite_denote input accepted initial

/-- Both emitted entries agree on the actual successor frame and entire buffer. -/
theorem lower_entryTransition_eq {graph : Graph args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (emitted : lower graph entry input = some programs)
    (guard : Bool) (initial : Buffer cells) :
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial :=
  Proofs.lower_entryTransition_eq input emitted guard initial

/-- The entry edit preserves the word and whole final buffer for either
predicate. Each artifact still executes entry, one arm, and the join. -/
theorem lower_runs {graph : Graph args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (emitted : lower graph entry input = some programs)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_runs input emitted guard fuel initial

/-- Success resolves the selected original version and certifies its overwrite
using the reader obligations inferred from the same table. -/
theorem rewriteSelected_checked {removeVersion : Nat} {result : Result args}
    (input : Tuple (Val cells) args) (accepted : rewriteSelected entry removeVersion input = some result) :
    result.candidate.removeVersion = removeVersion ∧
      discoverReaders entry removeVersion = some result.facts ∧
      Memory.DeadStore.Search.discover entry removeVersion result.facts = some result.candidate ∧
      Memory.DeadStore.rewrite entry result.candidate result.facts input = some result.graph :=
  Proofs.rewriteSelected_checked input accepted

/-- Exactly one Store disappears. All retained typed operands and their
relative operation order are preserved. -/
theorem rewriteSelected_operations {removeVersion : Nat} {result : Result args}
    (input : Tuple (Val cells) args) (accepted : rewriteSelected entry removeVersion input = some result) :
    DeletesStores 1 (operations entry) (operations result.graph) :=
  checked_operations input (rewriteSelected_checked input accepted).2.2.2

theorem rewriteSelected_denote {removeVersion : Nat} {result : Result args}
    (input : Tuple (Val cells) args) (accepted : rewriteSelected entry removeVersion input = some result)
    (initial : Heap cells) : result.graph.denote input initial = entry.denote input initial :=
  Proofs.rewriteSelected_denote input accepted initial

theorem lowerSelected_entryTransition_eq {graph : Graph args} {programs : Programs cells args} {removeVersion : Nat}
    (input : Tuple (Val cells) args) (emitted : lowerSelected graph entry removeVersion input = some programs)
    (guard : Bool) (initial : Buffer cells) :
    entryTransition programs.optimized programs.input guard initial =
      entryTransition programs.original programs.input guard initial :=
  Proofs.lowerSelected_entryTransition_eq input emitted guard initial

/-- Both emitted artifacts have the same three-block return observation
at either predicate and every initial buffer at the checked input. -/
theorem lowerSelected_runs {graph : Graph args} {programs : Programs cells args} {removeVersion : Nat}
    (input : Tuple (Val cells) args) (emitted : lowerSelected graph entry removeVersion input = some programs)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lowerSelected_runs input emitted guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry

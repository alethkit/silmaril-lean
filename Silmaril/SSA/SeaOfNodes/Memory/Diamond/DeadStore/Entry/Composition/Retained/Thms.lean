module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryTransition run)

variable {args : List ValueSort} {cells : Nat}

/-- Successful discovery preserves the word and heap for either guard
when the rewritten routes start from the retained Store's heap. -/
theorem rewrite_denote {graph : Graph args} {entry : Memory.Graph args} {edit : Edit args} {version : Nat}
    (input : Tuple (Val cells) args) (accepted : rewrite graph entry version input = some edit)
    (guard : Bool) (initial : Heap cells) :
    edit.routes.graph.denote guard input (edit.retained.table.denote input initial).2 =
      graph.denote guard input (entry.denote input initial).2 :=
  Proofs.rewrite_denote input accepted guard initial

theorem lower_refused (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args)
    (refused : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = none) :
    let repeated := Entry.lowerRepeated graph entry input
    lower graph entry version input = ⟨repeated.deleted, false, repeated.programs⟩ := by
  simp only [lower, refused]

/-- The actual optimized entry forwards the entire heap of the surviving Store. -/
theorem lower_retained_buffer (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) {edit : Edit args}
    (accepted : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = some edit)
    (guard : Bool) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    (entryTransition programs.optimized programs.input guard initial).2 =
      Buffer.mk (edit.retained.table.denote input initial.cell).2 :=
  Proofs.lower_retained_buffer graph entry version input accepted guard initial

/-- Both emitted artifacts return the original word and entire final buffer
in three CF steps for either predicate, with no return at shorter budgets. -/
theorem lower_runs (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_runs graph entry version input guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained

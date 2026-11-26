module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Proofs

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (cell)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryTransition lowerDiamond lowerDiamond_entryTransition lowerDiamond_run run)
open Memory.DeadStore.Search.Selection.Readers.Repeat renaming rewrite_denote → repeatDenote

variable {args : List ValueSort} {cells : Nat}
variable {entry : Memory.Graph args} {graph : Graph args} {edit : Edit args} {version : Nat}

private theorem stores_heap {first second : PrefixStore args} (found : stores entry = some (first, second))
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    (entry.denote input initial).2 = (second.table.denote input (first.table.denote input initial).2).2 := by
  unfold stores at found
  split at found <;> try contradiction
  cases Option.some.inj found
  rfl

private theorem swap_heap (first second : PrefixStore args) (input : Tuple (Val cells) args)
    (distinct : cell input first.address ≠ cell input second.address) (initial : Heap cells) :
    (first.table.denote input (second.table.denote input initial).2).2 =
      (second.table.denote input (first.table.denote input initial).2).2 :=
  (Function.update_comm (β := fun _ : Address cells => Word) distinct
    (input.get first.value) (input.get second.value) initial).symm

theorem rewrite_denote (input : Tuple (Val cells) args) (accepted : rewrite graph entry version input = some edit)
    (guard : Bool) (initial : Heap cells) :
    edit.routes.graph.denote guard input (edit.retained.table.denote input initial).2 =
      graph.denote guard input (entry.denote input initial).2 := by
  obtain ⟨⟨first, second⟩, found, checked⟩ := Option.bind_eq_some_iff.mp accepted
  change (if cell input first.address = cell input second.address then none else
    match version with
    | 1 => (Discovery.rewrite ⟨first, graph⟩ input).map (Edit.mk second)
    | 2 => (Discovery.rewrite ⟨second, graph⟩ input).map (Edit.mk first)
    | _ => none) = some edit at checked
  split at checked
  · contradiction
  next distinct =>
    split at checked
    · obtain ⟨result, routes, rfl⟩ := Option.map_eq_some_iff.mp checked
      exact (Discovery.rewrite_denote input routes guard (second.table.denote input initial).2).trans
        (congrArg (graph.denote guard input) ((swap_heap first second input distinct initial).trans
          (stores_heap found input initial).symm))
    · obtain ⟨result, routes, rfl⟩ := Option.map_eq_some_iff.mp checked
      exact (Discovery.rewrite_denote input routes guard (first.table.denote input initial).2).trans
        (congrArg (graph.denote guard input) (stores_heap found input initial).symm)
    · contradiction

theorem lower_runs (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected := by
  cases checked : rewrite graph (Entry.lowerRepeated graph entry input).entry version input with
  | none => simpa only [lower, checked] using Entry.lowerRepeated_runs graph entry input guard fuel initial
  | some edit =>
    simp only [lower, checked]
    refine ⟨(Entry.lowerRepeated_runs graph entry input guard fuel initial).1, ?_⟩
    have sameHeap := congrArg Prod.snd (repeatDenote entry input initial.cell)
    have same := (rewrite_denote input checked guard initial.cell).trans
      (congrArg (graph.denote guard input) sameHeap)
    exact (lowerDiamond_run edit.routes.graph (some edit.retained.table) input guard fuel initial).trans
      (congrArg (fun result : Word × Heap cells =>
        if fuel < 3 then none else some (result.1, Buffer.mk result.2)) same)

theorem lower_retained_buffer (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args)
    (accepted : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = some edit)
    (guard : Bool) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    (entryTransition programs.optimized programs.input guard initial).2 =
      Buffer.mk (edit.retained.table.denote input initial.cell).2 := by
  simp only [lower, accepted]
  exact congrArg Prod.snd (lowerDiamond_entryTransition edit.routes.graph (some edit.retained.table)
    input guard initial)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Proofs

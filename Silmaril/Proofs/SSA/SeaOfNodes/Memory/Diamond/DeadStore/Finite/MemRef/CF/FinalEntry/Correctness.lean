module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.Proofs

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe lower_run)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {entry retained : Memory.Graph args} {store : PrefixStore args}
variable {edit : Option (PrefixStore args × Memory.Graph args)}
variable {arm : Occurrence preds → Memory.Graph args} {candidate : Candidate args preds}
variable {suffix : Memory.Graph (.word :: args)} {input : Tuple (Val cells) args} {programs : Programs cells args preds}

theorem lowerCut_replay (emitted : lowerCut preds fits entry edit arm candidate suffix input = some programs) :
    ∃ (store : PrefixStore args) (retained : Memory.Graph args) (edited : Bank args preds),
      edit = some (store, retained) ∧
      Finite.check preds store arm candidate input = some edited ∧
      programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some retained) (fun i => edited[i.val]) suffix⟩ := by
  obtain ⟨⟨store, retained⟩, cut, remaining⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨edited, checked, packed⟩ := Option.bind_eq_some_iff.mp remaining
  exact ⟨store, retained, edited, cut, checked, (Option.some.inj packed).symm⟩

theorem lowerCut_entry (emitted : lowerCut preds fits entry edit arm candidate suffix input = some programs)
    (accepted : edit = some (store, retained)) (arrival : Occurrence preds) (initial : Buffer cells)
    (replay : entry.denote input initial.cell =
      ((retained.denote input initial.cell).1, (store.table.denote input (retained.denote input initial.cell).2).2)) :
    let exported := observe retained programs.input initial
    let originalBuffer := Buffer.mk (store.table.denote programs.input exported.2.cell).2
    observe entry programs.input initial = (exported.1, originalBuffer) ∧
      entryTransition programs.original programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, originalBuffer) ∧
      entryTransition programs.optimized programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, exported.2) := by
  obtain ⟨_, _, _, cut, _, rfl⟩ := lowerCut_replay emitted
  rw [accepted] at cut
  cases Option.some.inj cut
  refine ⟨?_, ?_, ?_⟩
  · simp only [lower_run]
    exact congrArg (fun result : Word × Heap cells => (result.1, Buffer.mk result.2)) replay
  · simp only [lowerBank_entry, lower_run, congrArg Prod.snd replay]
  · simp only [lowerBank_entry, lower_run]

theorem lowerCut_observations (emitted : lowerCut preds fits entry edit arm candidate suffix input = some programs)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells)
    (reapply : ∀ (store : PrefixStore args) (retained : Memory.Graph args), edit = some (store, retained) →
      (entry.denote input initial.cell).2 = (store.table.denote input (retained.denote input initial.cell).2).2) :
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    let packet := (arm arrival).denote input (entry.denote input initial.cell).2
    let result := suffix.denote (.cons packet.1 input) packet.2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.original programs.input arrival fuel initial = expected ∧
      run programs.optimized programs.input arrival fuel initial = expected := by
  obtain ⟨store, retained, edited, cut, checked, rfl⟩ := lowerCut_replay emitted
  have heap := reapply store retained cut
  have same : edited[arrival.val].denote input (Memory.Graph.denote retained input initial.cell).2 =
      (arm arrival).denote input (entry.denote input initial.cell).2 :=
    (Finite.check_observations checked arrival (Memory.Graph.denote retained input initial.cell).2).1.trans
      (congrArg ((arm arrival).denote input) heap.symm)
  simp only [lowerBank_entry, lowerBank_arm, lower_run, lowerBank_run, same, and_self]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.Proofs

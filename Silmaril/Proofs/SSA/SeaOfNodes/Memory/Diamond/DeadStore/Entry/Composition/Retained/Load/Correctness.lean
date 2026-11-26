module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Proofs

open RVSDG (Locals Tuple)
open Memory.Forwarding.Disjoint (Certificate cell)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (lowerDiamond lowerDiamond_entryTransition lowerDiamond_run entryTransition run)
open Memory.DeadStore.Search.Selection.Readers.Repeat renaming rewrite_denote → repeatDenote

variable {args : List ValueSort} {cells : Nat}

private theorem tail_transfer {past : List (List ValueSort)} {live : Nat} (tail : Memory.Body args past live)
    (selected : PrefixStore args) (input : Tuple (Val cells) args) (safe : checkTail selected input tail = true)
    (locals : Locals (Val cells) past) (initial : Heap cells) :
    let retained := tail.denote input locals initial
    tail.denote input locals (selected.table.denote input initial).2 =
      (retained.1, (selected.table.denote input retained.2).2) := by
  unfold checkTail at safe
  split at safe
  next _ _ _ reader writer stored returned _ _ _ =>
    let facts : Certificate args := ⟨selected.address, [reader, writer]⟩
    have valid := (facts.check_iff_valid input).mp safe
    have readSafe := valid reader List.mem_cons_self
    have writeSafe := valid writer (List.mem_cons_of_mem _ List.mem_cons_self)
    let written := initial.write (cell input selected.address) (input.get selected.value)
    let withRead (heap : Heap cells) : Locals (Val cells) ([.word] :: past) :=
      (.cons (heap.read (cell input reader)) .nil, locals)
    have same : withRead written = withRead initial :=
      congrArg (fun value : Word => ((.cons value .nil, locals) : Locals (Val cells) ([.word] :: past)))
        (initial.read_write_other (cell input selected.address) (cell input reader)
          (input.get selected.value) readSafe.symm)
    let word := readValue stored input (withRead initial)
    change (readValue returned input (withRead written),
        written.write (cell input writer) (readValue stored input (withRead written))) =
      (readValue returned input (withRead initial),
        (initial.write (cell input writer) word).write (cell input selected.address) (input.get selected.value))
    rw [same]
    exact congrArg (fun heap : Heap cells => (readValue returned input (withRead initial), heap))
      (Function.update_comm (β := fun _ : Address cells => Word) writeSafe (input.get selected.value) word initial)
  next => contradiction

theorem cut_denote {past : List (List ValueSort)} {live : Nat} {version : Nat}
    {body retained : Memory.Body args past live} {selected : PrefixStore args}
    (input : Tuple (Val cells) args) (accepted : cut version input body = some (selected, retained))
    (locals : Locals (Val cells) past) (initial : Heap cells) :
    let result := retained.denote input locals initial
    body.denote input locals initial = (result.1, (selected.table.denote input result.2).2) := by
  induction body generalizing initial with
  | ret => contradiction
  | load => contradiction
  | @store _ live _ address value rest ih =>
    cases address with
    | output => contradiction
    | arg address =>
      cases value with
      | output => contradiction
      | arg word =>
        simp only [cut] at accepted
        split at accepted
        · split at accepted
          next safe =>
            cases Option.some.inj accepted
            rw [Memory.DeadStore.reindexMemory_denote]
            exact tail_transfer rest ⟨address, word⟩ input safe locals initial
          next => contradiction
        · obtain ⟨⟨candidate, tail⟩, checked, packed⟩ := Option.map_eq_some_iff.mp accepted
          cases packed
          exact ih checked locals (initial.write (cell input address) (input.get word))

variable {graph : Graph args} {entry : Memory.Graph args} {edit : Retained.Edit args} {version : Nat}

theorem rewrite_checked (input : Tuple (Val cells) args) (accepted : rewrite graph entry version input = some edit) :
    ∃ selected, cut version input entry = some (selected, edit.retained) ∧
      Discovery.rewrite ⟨selected, graph⟩ input = some edit.routes := by
  obtain ⟨⟨selected, retained⟩, checked, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨routes, discovered, rfl⟩ := Option.map_eq_some_iff.mp rest
  exact ⟨selected, checked, discovered⟩

theorem rewrite_denote (input : Tuple (Val cells) args) (accepted : rewrite graph entry version input = some edit)
    (guard : Bool) (initial : Heap cells) :
    edit.routes.graph.denote guard input (edit.retained.denote input initial).2 =
      graph.denote guard input (entry.denote input initial).2 := by
  obtain ⟨_, checked, discovered⟩ := rewrite_checked input accepted
  exact (Discovery.rewrite_denote input discovered guard _).trans
    (congrArg (graph.denote guard input) (congrArg Prod.snd (cut_denote input checked PUnit.unit initial)).symm)

theorem lower_retained_entry (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args)
    (accepted : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = some edit)
    (guard : Bool) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    entryTransition programs.optimized programs.input guard initial =
      (.inl ⟨.arm (graph.merge.slot (SeaOfNodes.Diamond.Projection.ofBool guard)), .nil⟩,
        Buffer.mk (edit.retained.denote input initial.cell).2) := by
  obtain ⟨_, _, discovered⟩ := rewrite_checked input accepted
  simp only [lower, accepted]
  exact (lowerDiamond_entryTransition edit.routes.graph (some edit.retained) input guard initial).trans
    (by rw [Discovery.rewrite_merge input discovered])

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
    have same := (rewrite_denote input checked guard initial.cell).trans
      (congrArg (fun result : Word × Heap cells => graph.denote guard input result.2)
        (repeatDenote entry input initial.cell))
    exact (lowerDiamond_run edit.routes.graph (some edit.retained) input guard fuel initial).trans
      (congrArg (fun result : Word × Heap cells =>
        if fuel < 3 then none else some (result.1, Buffer.mk result.2)) same)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Proofs

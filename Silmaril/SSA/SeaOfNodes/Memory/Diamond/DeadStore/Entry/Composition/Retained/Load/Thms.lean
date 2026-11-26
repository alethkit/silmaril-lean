module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load

open RVSDG (Locals Tuple)
open SeaOfNodes.Diamond (Projection)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (entryTransition run)

variable {args : List ValueSort} {cells : Nat}

/-- The checked cut preserves the suffix's scalar result. Replaying only
the selected Store on the retained heap recovers the complete source heap. -/
theorem cut_denote {past : List (List ValueSort)} {live version : Nat}
    {body retained : Memory.Body args past live} {selected : PrefixStore args}
    (input : Tuple (Val cells) args) (accepted : cut version input body = some (selected, retained))
    (locals : Locals (Val cells) past) (initial : Heap cells) :
    let result := retained.denote input locals initial
    body.denote input locals initial = (result.1, (selected.table.denote input result.2).2) :=
  Proofs.cut_denote input accepted locals initial

/-- Success requires both the native entry cut and the existing two-route check. -/
theorem rewrite_checked {graph : Graph args} {entry : Memory.Graph args} {edit : Retained.Edit args} {version : Nat}
    (input : Tuple (Val cells) args) (accepted : rewrite graph entry version input = some edit) :
    ∃ selected, cut version input entry = some (selected, edit.retained) ∧
      Discovery.rewrite ⟨selected, graph⟩ input = some edit.routes :=
  Proofs.rewrite_checked input accepted

theorem lower_refused (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args)
    (refused : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = none) :
    let repeated := Entry.lowerRepeated graph entry input
    lower graph entry version input = ⟨repeated.deleted, false, repeated.programs⟩ := by
  simp only [lower, refused]

/-- The optimized entry emits the original Region frame and the full
buffer of the actual retained table, including its Load-dependent write. -/
theorem lower_retained_entry (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) {edit : Retained.Edit args}
    (accepted : rewrite graph (Entry.lowerRepeated graph entry input).entry version input = some edit)
    (guard : Bool) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    entryTransition programs.optimized programs.input guard initial =
      (.inl ⟨.arm (graph.merge.slot (Projection.ofBool guard)), .nil⟩,
        Buffer.mk (edit.retained.denote input initial.cell).2) :=
  Proofs.lower_retained_entry graph entry version input accepted guard initial

/-- Both emitted CFGs agree on the returned word and entire final buffer
for either guard and any initial buffer. Three CF block steps suffice. -/
theorem lower_runs (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (input : Tuple (Val cells) args) (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower graph entry version input).programs
    let result := graph.denote guard input (entry.denote input initial.cell).2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_runs graph entry version input guard fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load

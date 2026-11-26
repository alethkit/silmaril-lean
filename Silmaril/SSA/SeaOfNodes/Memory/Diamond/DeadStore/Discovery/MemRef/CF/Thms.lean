module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Projection)
open Silmaril.MLIR.MemRef (Buffer)

variable {cells : Nat} {args : List ValueSort}

theorem lower_eq_none_iff (source : Prefixed args) (input : Tuple (Val cells) args) :
    lower source input = none ↔ Discovery.rewrite source input = none := by
  cases checked : Discovery.rewrite source input <;> simp [lower, checked]

/-- Both emitted artifacts take the original incoming Region slot. -/
theorem lower_entry_slots {source : Prefixed args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (accepted : lower source input = some programs)
    (guard : Bool) (initial : Buffer cells) :
    let destination : Silmaril.MLIR.CF.Frame Label :=
      ⟨.arm (source.diamond.merge.slot (Projection.ofBool guard)), .nil⟩
    entryDestination programs.original programs.input guard initial = .inl destination ∧
      entryDestination programs.optimized programs.input guard initial = .inl destination :=
  Proofs.lower_entry_slots input accepted guard initial

/-- Three block steps reach the return in either artifact. The observation
includes the returned word and every final cell at the checked input. -/
theorem lower_runs {source : Prefixed args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (accepted : lower source input = some programs)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    let result := source.denote guard input initial.cell
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    run programs.original programs.input guard fuel initial = expected ∧
      run programs.optimized programs.input guard fuel initial = expected :=
  Proofs.lower_runs input accepted guard fuel initial

theorem run_optimized_eq_original {source : Prefixed args} {programs : Programs cells args}
    (input : Tuple (Val cells) args) (accepted : lower source input = some programs)
    (guard : Bool) (fuel : Nat) (initial : Buffer cells) :
    run programs.optimized programs.input guard fuel initial =
      run programs.original programs.input guard fuel initial :=
  let both := lower_runs input accepted guard fuel initial
  both.2.trans both.1.symm

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF

module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Proofs

open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.MLIR.Finite (Profile encodeResult encodeResult_injective)
open Loop.Institution (Equation)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {P : EntrySignature}

/-- Equality of CF observations reflects equality of the native partial
records because every returned cell and the word are encoded injectively. -/
theorem satisfaction (e : Equation P) (model : EntryModel P) : Holds e model ↔ e.Holds model := by
  refine forall_congr' fun initial => ?_
  unfold observe
  dsimp only
  erw [lower_denotePart (Profile.ofCells model.cells) e.lhs model.input initial,
    lower_denotePart (Profile.ofCells model.cells) e.rhs model.input initial]
  let encode := fun result : Word × Heap model.cells =>
    Outcome.returned (encodeResult (Profile.ofCells model.cells) result.1 result.2)
  change (e.lhs.denote model.input initial).map encode =
    (e.rhs.denote model.input initial).map encode ↔ _
  have injective : Function.Injective encode :=
    fun _ _ equal => encodeResult_injective (Profile.ofCells model.cells) (Outcome.returned.inj equal)
  refine ⟨fun equal => Part.ext (fun result => ?_), congrArg (Part.map encode)⟩
  constructor
  · intro native
    have target := Part.mem_map encode native
    rw [equal] at target
    obtain ⟨other, native', same⟩ := (Part.mem_map_iff _).1 target
    exact (injective same) ▸ native'
  · intro native
    have target := Part.mem_map encode native
    rw [← equal] at target
    obtain ⟨other, native', same⟩ := (Part.mem_map_iff _).1 target
    exact (injective same) ▸ native'

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Proofs

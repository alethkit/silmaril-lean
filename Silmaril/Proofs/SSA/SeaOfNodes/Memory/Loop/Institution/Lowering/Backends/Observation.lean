module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Proofs

open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.MLIR.Finite (Profile evalOp)
open Memory.Diamond.MLIR.Finite renaming encodeResult → encodeCFResult
open Silmaril.MLIR.CF.SwitchAssert (Cfg Outcome)

variable {P : EntrySignature}

theorem mlir_observation_iff_run (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    MLIR.Institution.observe graph model initial =
      Part.some (.returned (encodeCFResult (Profile.ofCells model.cells) word final)) ↔
      ∃ fuel, (MLIR.lower (Profile.ofCells model.cells) graph).run evalOp fuel
        (MLIR.encodeEntry (Profile.ofCells model.cells) model.input initial) =
          some (encodeCFResult (Profile.ofCells model.cells) word final) := by
  unfold MLIR.Institution.observe
  dsimp only
  erw [Cfg.denotePart_eq_some_iff]
  simp only [Cfg.embed_run, Option.map_eq_some_iff, Outcome.returned.injEq]
  constructor
  · rintro ⟨fuel, output, run, rfl⟩
    exact ⟨fuel, run⟩
  · rintro ⟨fuel, run⟩
    exact ⟨fuel, _, run, rfl⟩

theorem mlir_no_return_iff (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    MLIR.Institution.observe graph model initial = Part.none ↔ graph.denote model.input initial = Part.none := by
  unfold MLIR.Institution.observe
  erw [Cfg.denotePart_eq_none_iff, Cfg.embed_diverges_iff,
    MLIR.lower_diverges_iff (Profile.ofCells model.cells) graph model.input initial]
  exact Part.eq_none_iff'.symm

theorem mlir_observation_eq_map_theta (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    MLIR.Institution.observe graph model initial =
      (thetaObservation graph model initial).map (fun result =>
        Outcome.returned (encodeCFResult (Profile.ofCells model.cells)
          (result.get .head) (result.get (.tail .head)))) := by
  erw [MLIR.Institution.observe_eq graph model initial, theta_observation graph model initial, Part.map_map]
  rfl

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Proofs

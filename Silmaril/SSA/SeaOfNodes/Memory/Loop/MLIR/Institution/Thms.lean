module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Correspondence

/-! Satisfaction of emitted CFG equations over the native typed entry models. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution

open CategoryTheory
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.MLIR.Finite (Profile encodeResult)
open Loop.Institution (Equation mapGraph denote_mapGraph)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {P Q : EntrySignature}

/-- The observation includes divergence and the entire returned heap. -/
theorem observe_eq (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    observe graph model initial = (graph.denote model.input initial).map
      (fun result => Outcome.returned (encodeResult (Profile.ofCells model.cells) result.1 result.2)) :=
  lower_denotePart (Profile.ofCells model.cells) graph model.input initial

/-- Re-emission after a typed entry map agrees observationally with
pulling back the input valuation. The cell count and initial heap are shared. -/
theorem observe_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q) (initial : Heap model.cells) :
    observe (mapGraph h graph) model initial = observe graph (reduct h model) initial := by
  erw [observe_eq (mapGraph h graph) model initial, observe_eq graph (reduct h model) initial,
    denote_mapGraph h graph model initial]
  rfl

/-- Equality of the actual CFG observations preserves and reflects native
satisfaction at every typed model, at its own finite cell count. -/
theorem satisfaction (e : Equation P) (model : EntryModel P) : Holds e model ↔ e.Holds model :=
  Proofs.satisfaction e model

theorem satisfaction_reindex (h : P ⟶ Q) (e : Equation P) (model : EntryModel Q) :
    Holds (e.map h) model ↔ Holds e (reduct h model) :=
  (satisfaction _ _).trans ((e.satisfaction h model).trans (satisfaction _ _).symm)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution

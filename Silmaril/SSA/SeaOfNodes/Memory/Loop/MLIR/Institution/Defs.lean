module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs

/-! Observe the actual generated CFGs at native typed models. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution

open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.MLIR.Finite (Profile evalOp resultTypes)
open Loop.Institution (Equation)
open Silmaril.MLIR.CF.SwitchAssert (Cfg Outcome)

variable {P : EntrySignature}

/-- Use the canonical scalar profile at the model's cell count and the
existing partial CF observation at its encoded input and initial heap. -/
noncomputable def observe (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    Part (Outcome (resultTypes (Profile.ofCells model.cells))) :=
  let profile := Profile.ofCells model.cells
  (Cfg.embed (lower profile graph)).denotePart evalOp (encodeEntry profile model.input initial)

/-- Compare both emitted CFGs on every initial heap at the typed model. -/
def Holds (e : Equation P) (model : EntryModel P) : Prop :=
  ∀ initial, observe e.lhs model initial = observe e.rhs model initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution

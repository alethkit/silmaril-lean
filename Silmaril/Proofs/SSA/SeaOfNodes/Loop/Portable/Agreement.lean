module

public import Silmaril.SSA.SeaOfNodes.Loop.Portable.Defs
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.Portable.Proofs

open SeaOfNodes.MLIR (sourceInputs)
open Silmaril.MLIR.Arith (Env Width)

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

theorem agreement (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) (input : Env Γ) :
    Agreement g input where
  lambda_eval_iff label payload := by
    refine (LambdaSSA.Generic.lower_eval_iff g Loop.MLIR.CF.model
      (sourceInputs input) () () label payload).trans ?_
    have returns := g.returns_iff_mem_denote Loop.MLIR.CF.model (sourceInputs input)
    constructor
    · rintro ⟨value, returned, exit, result, _⟩
      exact ⟨value, (returns value).mp returned, exit, result⟩
    · rintro ⟨value, observed, exit, result⟩
      exact ⟨value, (returns value).mpr observed, exit, result, rfl⟩
  theta := Theta.Institution.lowerTheta_observe g Loop.MLIR.CF.model (sourceInputs input)
  cf := Loop.MLIR.CF.lower_denotePart g input

end Silmaril.SSA.SeaOfNodes.Loop.Portable.Proofs

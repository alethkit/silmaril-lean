module

public import Silmaril.SSA.MLIR.Tensor.Defs

public section

namespace Silmaril.Proofs.MLIR.Tensor

open Silmaril.MLIR.Tensor

theorem false_of_zero_dim {shape : Shape} (h : 0 ∈ shape) (i : Index shape) : False := by
  induction shape with
  | nil => exact List.not_mem_nil h
  | cons extent shape ih =>
    rcases List.mem_cons.mp h with head | tail
    · subst extent
      exact Fin.elim0 i.1
    · exact ih tail i.2

end Silmaril.Proofs.MLIR.Tensor

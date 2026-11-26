module

public import Silmaril.SSA.SeaOfNodes.Loop.Portable.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.Portable.Agreement

/-! The three actual target observations agree through the native partial result. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.Portable

open Silmaril.MLIR.Arith (Env Width)

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- Uniform finite-return and exact partial agreement on the common CF profile. -/
theorem agreement (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) (input : Env Γ) :
    Agreement g input :=
  Proofs.agreement g input

end Silmaril.SSA.SeaOfNodes.Loop.Portable

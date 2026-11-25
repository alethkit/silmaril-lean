module

public import Silmaril.SSA.MLIR.Affine.Defs
import Silmaril.Proofs.SSA.MLIR.Affine.Fold

public section

namespace Silmaril.MLIR.Affine

universe u

variable {dims symbols : Nat} {State : Type u}

/-- The fold result is exactly the one admitted by the source loop semantics. -/
theorem ForLoop.runs_iff_fold (loop : ForLoop dims symbols State)
    (d : Fin dims → Int) (s : Fin symbols → Int) (init out : State) :
    loop.Runs d s init out ↔ out = loop.fold d s init :=
  Proofs.MLIR.Affine.runs_iff_fold _ _ _ _ _ _

/-- If the lower bound meets or exceeds the upper bound, keep the initial values. -/
theorem ForLoop.fold_of_ge (loop : ForLoop dims symbols State)
    (d : Fin dims → Int) (s : Fin symbols → Int) (init : State)
    (h : loop.upper.eval d s ≤ loop.lower.eval d s) : loop.fold d s init = init :=
  ((loop.runs_iff_fold d s init init).mp (.done h)).symm

end Silmaril.MLIR.Affine

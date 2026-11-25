module

public import Silmaril.SSA.MLIR.Institution.Translation.Examples.Defs

public section

namespace Silmaril.Proofs.MLIR.Institution.Translation.Examples

open Silmaril.MLIR.Institution
open Silmaril.MLIR.Institution.Translation.Examples

theorem lower_reduct : lower.reduct Arith.model = model := by
  change Model.mk (S := signature) Arith.model.carrier (fun {_ _} op => _) =
    Model.mk (S := signature) Arith.model.carrier (fun {_ _} op => _)
  congr 1
  funext a p op args bodies i
  cases op with
  | core => rfl
  | double w =>
    let x : BitVec w.val := args 0
    change x * BitVec.ofNat w.val 2 = x + x
    exact BitVec.mul_two

end Silmaril.Proofs.MLIR.Institution.Translation.Examples

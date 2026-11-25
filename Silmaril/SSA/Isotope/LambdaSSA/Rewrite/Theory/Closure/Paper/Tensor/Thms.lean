module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Tensor

/-! # Singleton whiskering laws in the paper relation

These representative-level equations consume the selected generators and
context rules in `Paper.Eqv`. The composition laws use constructor-pair β
under a singleton continuation and under the original unpacking. The
identity laws use the variable product η step directly.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

open CfgEta.TypeCategory (whiskerLeftRegion whiskerRightRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {A B C : τ} {r s : Region Φ}

/-- Sequencing two left whiskerings is equivalent to left whiskering their sequence. -/
theorem whiskerLeftRegion_comp (X : τ) (hr : ValueBranches [A] r [B])
    (hs : ValueBranches [B] s [C]) :
    Eqv [Silmaril.product X A]
      (compLSubst (fun _ => whiskerLeftRegion r) (fun _ => whiskerLeftRegion s) 0)
      (whiskerLeftRegion (compLSubst (fun _ => r) (fun _ => s) 0)) [Silmaril.product X C] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Tensor.whiskerLeftRegion_comp X hr hs

/-- Sequencing two right whiskerings is equivalent to right whiskering their sequence. -/
theorem whiskerRightRegion_comp (X : τ) (hr : ValueBranches [A] r [B])
    (hs : ValueBranches [B] s [C]) :
    Eqv [Silmaril.product A X]
      (compLSubst (fun _ => whiskerRightRegion r) (fun _ => whiskerRightRegion s) 0)
      (whiskerRightRegion (compLSubst (fun _ => r) (fun _ => s) 0)) [Silmaril.product C X] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Tensor.whiskerRightRegion_comp X hr hs

/-- A left-whiskered forwarding branch takes one variable product η step. -/
theorem whiskerLeftRegion_id (X A : τ) :
    Eqv [Silmaril.product X A] (whiskerLeftRegion (.br 0 (.var 0) : Region Φ))
      (.br 0 (.var 0)) [Silmaril.product X A] :=
  .productEta (.let₂Eta rfl rfl)

/-- A right-whiskered forwarding branch takes one variable product η step. -/
theorem whiskerRightRegion_id (X A : τ) :
    Eqv [Silmaril.product A X] (whiskerRightRegion (.br 0 (.var 0) : Region Φ))
      (.br 0 (.var 0)) [Silmaril.product A X] :=
  .productEta (.let₂Eta rfl rfl)

end Silmaril.Isotope.LambdaSSA.Region.Paper

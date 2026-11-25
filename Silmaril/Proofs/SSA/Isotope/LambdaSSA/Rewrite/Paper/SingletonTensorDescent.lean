module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Transport.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Defs

/-! # Whiskering respects guarded singleton representatives -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensorDescent

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper (Eqv)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (whiskerLeftRegion whiskerRightRegion)
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ} {r s : Region Φ}

theorem left_congr (X : τ) (h : Eqv [A] r s [B])
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B]) :
    Eqv [Silmaril.product X A] (whiskerLeftRegion r) (whiskerLeftRegion s) [Silmaril.product X B] := by
  have ren : Ren [A] [A, X, Silmaril.product X A] (lift (Nat.succ ∘ Nat.succ)) :=
    (((Ren.wk [] (Silmaril.product X A)).comp (Ren.wk _ X)).lift A)
  refine .let₂ (.var rfl) (.lsubstPost (h.renameVars ren) (hr.renameVars ren) (hs.renameVars ren) ?_)
  intro i D hi
  cases List.mem_singleton.mp (List.mem_of_getElem? hi)
  exact .br rfl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))

theorem right_congr (X : τ) (h : Eqv [A] r s [B])
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B]) :
    Eqv [Silmaril.product A X] (whiskerRightRegion r) (whiskerRightRegion s) [Silmaril.product B X] := by
  have ren : Ren [A] [X, A, Silmaril.product A X] (Nat.succ ∘ lift Nat.succ) :=
    (((Ren.wk [] (Silmaril.product A X)).lift A).comp (Ren.wk _ X))
  refine .let₂ (.var rfl) (.lsubstPost (h.renameVars ren) (hr.renameVars ren) (hs.renameVars ren) ?_)
  intro i D hi
  cases List.mem_singleton.mp (List.mem_of_getElem? hi)
  exact .br rfl (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensorDescent

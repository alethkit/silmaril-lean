module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Defs

/-! # Representatives for a retained unary let -/

@[expose] public section

open Silmaril
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open CfgEta.TypeCategory
open Silmaril.DeBruijn (lift)

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B : τ} {a : Tm Φ} {r : Region Φ}

/-- Evaluate the scrutinee once and forward its bound result. -/
def returnOnce (a : Tm Φ) : Region Φ :=
  .let₁ a (.br 0 (.var 0))

/-- Return two copies of the input value. -/
def diagonal : Region Φ :=
  .br 0 (.pair (.var 0) (.var 0))

/-- Recover the retained input and the scrutinee value before running the body. -/
def unpackBody (r : Region Φ) : Region Φ :=
  .let₂ (.var 0) (r.renameVars (lift (lift Nat.succ)))

theorem returnOnce_typed (ha : Tm.HasType [X] a A) :
    ValueBranches [X] (returnOnce a) [A] :=
  .let₁ ha (.br rfl (.var (i := 0) rfl))

theorem diagonal_typed (X : τ) :
    ValueBranches [X] (diagonal : Region Φ) [Silmaril.product X X] :=
  .br rfl (.pair (.var (i := 0) rfl) (.var (i := 0) rfl))

theorem unpackBody_typed (hr : ValueBranches [A, X] r [B]) :
    ValueBranches [Silmaril.product X A] (unpackBody r) [B] :=
  .let₂ (.var (i := 0) rfl)
    (hr.renameVars (((Ren.wk ([] : VCtx τ) (Silmaril.product X A)).lift X).lift A))

end Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet

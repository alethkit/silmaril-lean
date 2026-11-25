module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Defs

/-! # Typing and quotient descent of computation whiskering -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Tensor

open CategoryTheory Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Region.CfgEta (Eqv toHom_eq_iff)
open Region.CfgEta.TypeCategory
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {A B : τ} {r s : Region Φ}

private theorem leftRen (X A : τ) :
    Ren [A] [A, X, Silmaril.product X A] (lift (Nat.succ ∘ Nat.succ)) :=
  (((Ren.wk [] (Silmaril.product X A)).comp (Ren.wk _ X)).lift A)

private theorem rightRen (A X : τ) :
    Ren [A] [X, A, Silmaril.product A X] (Nat.succ ∘ lift Nat.succ) :=
  (((Ren.wk [] (Silmaril.product A X)).lift A).comp (Ren.wk _ X))

private theorem leftReturn (X A B : τ) :
    LSubst.ValueFamily (Φ := Φ) [A, X, Silmaril.product X A] [B] [Silmaril.product X B]
      (fun _ => .br 0 (.pair (.var 2) (.var 0))) := by
  intro i D hi
  cases List.mem_singleton.mp (List.mem_of_getElem? hi)
  exact .br rfl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))

private theorem rightReturn (A B X : τ) :
    LSubst.ValueFamily (Φ := Φ) [X, A, Silmaril.product A X] [B] [Silmaril.product B X]
      (fun _ => .br 0 (.pair (.var 0) (.var 1))) := by
  intro i D hi
  cases List.mem_singleton.mp (List.mem_of_getElem? hi)
  exact .br rfl (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))

theorem whiskerLeftRegion_typed (X : τ) (hr : ValueBranches [A] r [B]) :
    ValueBranches [Silmaril.product X A] (whiskerLeftRegion r) [Silmaril.product X B] :=
  .let₂ (.var rfl) ((hr.renameVars (leftRen X A)).lsubst (leftReturn X A B))

theorem whiskerRightRegion_typed (X : τ) (hr : ValueBranches [A] r [B]) :
    ValueBranches [Silmaril.product A X] (whiskerRightRegion r) [Silmaril.product B X] :=
  .let₂ (.var rfl) ((hr.renameVars (rightRen A X)).lsubst (rightReturn A B X))

theorem whiskerLeftRegion_congr (X : τ) (h : Eqv [A] r s [B]) :
    Eqv [Silmaril.product X A] (whiskerLeftRegion r) (whiskerLeftRegion s) [Silmaril.product X B] :=
  .let₂ (.var rfl) ((h.renameVars (leftRen X A)).lsubst (fun _ _ hi => (leftReturn X A B hi).hasType))

theorem whiskerRightRegion_congr (X : τ) (h : Eqv [A] r s [B]) :
    Eqv [Silmaril.product A X] (whiskerRightRegion r) (whiskerRightRegion s) [Silmaril.product B X] :=
  .let₂ (.var rfl) ((h.renameVars (rightRen A X)).lsubst (fun _ _ hi => (rightReturn A B X hi).hasType))

theorem liftSingleton_respects {X Y P Q : τ} {transform : Region Φ → Region Φ}
    (typed : ∀ {r}, ValueBranches [X] r [Y] → ValueBranches [P] (transform r) [Q])
    (congr : ∀ {r s}, Eqv [X] r s [Y] → Eqv [P] (transform r) (transform s) [Q])
    {a b : ContinuationFamily [] [X] [Y]} (h : Region.CfgEta.Equivalent [] [X] [Y] a.val b.val) :
    ofRegion (Γ := []) (typed (a.property (ℓ := 0) rfl)) =
      ofRegion (Γ := []) (typed (b.property (ℓ := 0) rfl)) := by
  apply InducedCategory.hom_ext
  apply toHom_eq_iff.mpr
  intro i D hi
  cases List.mem_singleton.mp (List.mem_of_getElem? hi)
  exact congr (h (i := 0) rfl)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Tensor

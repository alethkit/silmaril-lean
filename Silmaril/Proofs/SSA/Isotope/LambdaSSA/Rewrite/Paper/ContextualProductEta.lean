module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms

/-! # Product η in a typed continuation context -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ContextualProductEta

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper (Eqv splitProduct)
open Silmaril.DeBruijn (lift)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private def useReplacement (i : Nat) (j : Nat) : Tm Φ :=
  if j = i then .var 0 else .var (j + 1)

private theorem useReplacement_typed {Γ : VCtx τ} {P : τ} {i : Nat} (hi : At Γ i P) :
    Tm.Subst.HasType (Φ := Φ) Γ (P :: Γ) (useReplacement i) := by
  intro j T hj
  by_cases h : j = i
  · subst j
    cases Option.some.inj (hj.symm.trans hi)
    simpa [useReplacement] using
      (Tm.HasType.var (Φ := Φ) (Γ := P :: Γ) (i := 0) (A := P) rfl)
  · simp only [useReplacement, ite_eq_right h]
    exact .var hj

private theorem split_eq {r : Region Φ} (i : Nat) :
    (.let₂ (.var i) (.br 0 (.pair (.var 1) (.var 0))) : Region Φ).lsubst
        (fun _ => r.substVars (useReplacement i)) =
      .let₂ (.var i) (r.substVars (splitProduct i)) := by
  simp only [lsubst, liftLSubstVars, renameVars_substVars, substVars_comp]
  congr 2
  funext j
  by_cases h : j = i <;>
    simp only [useReplacement, splitProduct, h, ite_true, ite_false, Tm.rename, lift, Tm.subst,
      Tm.singleSubst, Tm.consSubst]

private theorem substituteOriginal_eq {r : Region Φ} (i : Nat) :
    (.br 0 (.var i) : Region Φ).lsubst (fun _ => r.substVars (useReplacement i)) = r := by
  simp only [lsubst, substVars_comp]
  have e : (fun j => (useReplacement (Φ := Φ) i j).subst (Tm.singleSubst (.var i))) = Tm.var := by
    funext j
    by_cases h : j = i <;>
      simp only [useReplacement, h, ite_true, ite_false, Tm.subst, Tm.singleSubst, Tm.consSubst]
  rw [e, substVars_var]

theorem product_variable_eta_context {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {i : Nat} {A B : τ} (hi : At Γ i (product A B)) (hr : HasType Γ r L) :
    Eqv Γ (.let₂ (.var i) (r.substVars (splitProduct i))) r L := by
  let P := product A B
  have source : ValueBranches Γ (.let₂ (.var i)
      (.br 0 (.pair (.var 1) (.var 0))) : Region Φ) [P] :=
    .let₂ (.var hi) (.br rfl (.pair (.var rfl) (.var rfl)))
  have target : ValueBranches Γ (.br 0 (.var i) : Region Φ) [P] := .br rfl (.var hi)
  have after : LSubst.HasType Γ [P] L (fun _ => r.substVars (useReplacement i)) := by
    intro j D hj
    cases List.mem_singleton.mp (List.mem_of_getElem? hj)
    exact hr.substVars (useReplacement_typed hi)
  have e := Eqv.lsubstPost (.productEta (.let₂Eta hi rfl)) source target after
  rwa [split_eq, substituteOriginal_eq] at e

private theorem product_variable_eta_reflect {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    {i : Nat} {A B : τ} (hi : At Γ i (product A B)) (hr : HasType Γ r L) (hs : HasType Γ s L)
    (h : Eqv (B :: A :: Γ) (r.substVars (splitProduct i)) (s.substVars (splitProduct i)) L) :
    Eqv Γ r s L :=
  (product_variable_eta_context hi hr).symm.trans
    ((Eqv.let₂ (.var hi) h).trans (product_variable_eta_context hi hs))

omit [HasTy Φ τ] in
private theorem splitProduct_typed {Γ : VCtx τ} {i : Nat} {A B : τ} (hi : At Γ i (product A B)) :
    ∀ ⦃j D⦄, At Γ j D → Tm.BranchValue (B :: A :: Γ) (splitProduct (Φ := Φ) i j) D := by
  intro j D hj
  by_cases h : j = i
  · subst j
    cases Option.some.inj (hj.symm.trans hi)
    simpa [splitProduct] using
      (Tm.BranchValue.pair (.var (i := 1) rfl) (.var (i := 0) rfl) :
        Tm.BranchValue (B :: A :: Γ) (.pair (.var 1) (.var 0) : Tm Φ) (product A B))
  · simp only [splitProduct, ite_eq_right h]
    exact .var hj

theorem product_variable_eta_iff {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    {i : Nat} {A B : τ} (hi : At Γ i (product A B)) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    Eqv (B :: A :: Γ) (r.substVars (splitProduct i)) (s.substVars (splitProduct i)) L ↔
      Eqv Γ r s L :=
  ⟨product_variable_eta_reflect hi hr hs, fun h => h.substVars (splitProduct_typed hi)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ContextualProductEta

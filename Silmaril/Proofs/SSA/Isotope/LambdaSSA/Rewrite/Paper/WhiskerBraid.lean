module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms

/-! # Swapping the factors of a Paper whiskered computation -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WhiskerBraid

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper (Eqv lsubst_singleton_congr)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
  (whiskerLeftRegion whiskerRightRegion whiskerLeftBody whiskerRightBody whiskerLeftBody_typed
    whiskerLeftRegion_typed whiskerRightRegion_typed)
open Silmaril.DeBruijn (lift)
open CategoryTheory
open Paper.TypeCategory

universe u v

variable {Φ : Type v}

private abbrev seq (r s : Region Φ) : Region Φ := compLSubst (fun _ => r) (fun _ => s) 0
private abbrev rightRen : Nat → Nat := Nat.succ ∘ lift Nat.succ
private abbrev pairSwap : Tm Φ := .pair (.var 0) (.var 1)

private abbrev addCapture : Nat → Nat := lift (lift (lift Nat.succ))
private abbrev insertCaptures : Nat → Nat := addCapture ∘ addCapture ∘ addCapture

private def prepareBody (r : Region Φ) : Region Φ :=
  (r.renameVars insertCaptures).substVars
    (Tm.liftSubst (Tm.liftSubst (Tm.singleSubst pairSwap)))

private theorem right_then_swap (r : Region Φ) :
    seq (whiskerRightRegion r) braidRegion =
      .let₂ (.var 0) ((r.renameVars rightRen).lsubst
        (fun _ => .let₂ pairSwap (.br 0 pairSwap))) := by
  unfold seq whiskerRightRegion whiskerRightBody
  rw [compLSubst, lsubst, lsubst_comp]
  rfl

private theorem swap_then (s : Region Φ) :
    seq braidRegion (.let₂ (.var 0) s) =
      .let₂ (.var 0) (.let₂ pairSwap (prepareBody s)) := by
  simp only [braidRegion, compLSubst, lsubst, liftLSubstVars, renameVars, Tm.rename, lift, substVars,
    Tm.subst, Tm.singleSubst, Tm.consSubst, renameVars_comp, prepareBody, addCapture, insertCaptures]
  rfl

private theorem swap_left_beta (r : Region Φ) :
    (prepareBody (whiskerLeftBody r)).substVars (Tm.consSubst (.var 1) (Tm.singleSubst (.var 0))) =
      (r.renameVars rightRen).lsubst (fun _ => .br 0 (.pair (.var 1) (.var 0))) := by
  simp only [prepareBody, whiskerLeftBody, substVars_comp, substVars_renameVars, substVars_lsubst]
  rw [renameVars_eq_substVars]
  congr 2
  funext i
  cases i <;> rfl

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

omit [TypeFormers τ] in
private theorem addCapture_typed (Γ : VCtx τ) (D a b c : τ) :
    Ren (a :: b :: c :: Γ) (a :: b :: c :: D :: Γ) addCapture :=
  (((Ren.wk Γ D).lift c).lift b).lift a

omit [TypeFormers τ] in
private theorem insertCaptures_typed (T U V a b c : τ) :
    Ren [a, b, c] [a, b, c, T, U, V] insertCaptures :=
  (addCapture_typed [] V a b c).comp
    ((addCapture_typed [V] U a b c).comp (addCapture_typed [U, V] T a b c))

private theorem swap_natural_region {A B : τ} {r : Region Φ} (X : τ)
    (hr : ValueBranches [A] r [B]) :
    Eqv [product A X] (seq (whiskerRightRegion r) braidRegion)
      (seq braidRegion (whiskerLeftRegion r)) [product X B] := by
  rw [right_then_swap]
  unfold whiskerLeftRegion
  rw [swap_then]
  apply Eqv.let₂ (A := A) (B := X) (.var rfl)
  let body := (r.renameVars rightRen).lsubst (fun _ => .br 0 (.pair (.var 1) (.var 0)))
  apply Eqv.trans (s := body)
  · dsimp only [body]
    apply lsubst_singleton_congr (hr.renameVars
      ((((Ren.wk [] (product A X)).lift A).comp (Ren.wk _ X)) :
        Ren [A] [X, A, product A X] rightRen))
    have a : Tm.BranchValue [B, X, A, product A X] (.var 0 : Tm Φ) B := .var rfl
    have b : Tm.BranchValue [B, X, A, product A X] (.var 1 : Tm Φ) X := .var rfl
    exact .productBeta (.let₂Beta a b (.br rfl (.pair (.var rfl) (.var rfl))))
  · dsimp only [body]
    apply Eqv.symm
    rw [← swap_left_beta]
    have x : Tm.BranchValue [X, A, product A X] (.var 0 : Tm Φ) X := .var rfl
    have a : Tm.BranchValue [X, A, product A X] (.var 1 : Tm Φ) A := .var rfl
    apply Eqv.productBeta
    apply ProductBeta.Step.let₂Beta x a
    have h := (whiskerLeftBody_typed X hr).hasType.renameVars
      (insertCaptures_typed X A (product A X) A X (product X A))
    exact h.substVars (((Tm.Subst.HasType.single (.pair x.hasType a.hasType)).lift X).lift A)

private theorem swap_swap_region (A B : τ) :
    Eqv [product A B] (seq braidRegion braidRegion : Region Φ) (.br 0 (.var 0)) [product A B] := by
  change Eqv [product A B] (seq braidRegion (.let₂ (.var 0) (.br 0 pairSwap)) : Region Φ) _ _
  rw [swap_then]
  apply Eqv.trans (s := .let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0))))
  · apply Eqv.let₂ (A := A) (B := B) (.var rfl)
    exact .productBeta (.let₂Beta
      (.var (i := 0) rfl : Tm.BranchValue [B, A, product A B] _ B)
      (.var (i := 1) rfl : Tm.BranchValue [B, A, product A B] _ A)
      (.br rfl (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))))
  · exact .productEta (.let₂Eta rfl rfl)

private theorem seq_typed {A B D : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [B] s [D]) :
    ValueBranches [A] (seq r s) [D] := by
  have first : LSubst.ValueFamily [] [A] [B] (fun _ => r) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hr
  have second : LSubst.ValueFamily [] [B] [D] (fun _ => s) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hs
  exact (first.comp second) (ℓ := 0) rfl

theorem whiskerRight_braid {A B : τ} (X : τ) (f : ofType (Φ := Φ) A ⟶ ofType B) :
    whiskerRight f (ofType X) ≫ braid B X = braid A X ≫ whiskerLeft (ofType X) f := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion (A := A) (B := B) f
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion]
  unfold braid tensorObj
  rw [ofRegion_comp _ _ (seq_typed (whiskerRightRegion_typed X hr) (braidBranches B X)),
    ofRegion_comp _ _ (seq_typed (braidBranches A X) (whiskerLeftRegion_typed X hr))]
  exact (ofRegion_eq_iff _ _).mpr (swap_natural_region X hr)

theorem braid_braid (A B : τ) : braid (Φ := Φ) A B ≫ braid B A = 𝟙 (ofType (product A B)) := by
  unfold braid
  rw [ofRegion_comp _ _ (seq_typed (braidBranches A B) (braidBranches B A))]
  exact ((ofRegion_eq_iff _ _).mpr (swap_swap_region A B)).trans (ofRegion_id (product A B))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WhiskerBraid

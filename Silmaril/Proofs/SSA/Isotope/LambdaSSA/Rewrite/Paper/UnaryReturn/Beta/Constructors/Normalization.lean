module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Constructors

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.UnaryReturn Paper.RetainedLet
open Paper.TypeCategory Paper.BoundSimulation
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A B D : τ} {t c : Tm Φ}
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

omit [HasTy Φ τ] in
theorem pure {ε : Type w} [HasEff Φ ε] (pe : ε) (h : Normalizes Γ t c D) :
    Tm.Pure pe t := by
  induction h with
  | value hc => exact (BetaNormalizes.value hc).pure pe
  | let₁ _ _ ha hb => exact .let₁ ha hb
  | pair _ _ ha hb => exact .pair ha hb
  | inl _ ha => exact .inl ha
  | inr _ ha => exact .inr ha

private theorem bind_eq_subst {r : Region Φ} {L : LCtx τ}
    (h : Paper.Extension.Eqv Seed Γ (returnOnce t) (.br 0 c) [D])
    (ht : Tm.HasType Γ t D) (hc : Tm.BranchValue Γ c D) (hr : HasType (D :: Γ) r L) :
    Paper.Extension.Eqv Seed Γ (.let₁ t r) (r.substVars (Tm.singleSubst c)) L := by
  have family : LSubst.HasType Γ [D] L (fun _ => r) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hr
  have step := h.lsubstPost (returnOnce_valueBranches ht) (.br (ℓ := 0) rfl hc) family
  change Paper.Extension.Eqv Seed Γ
    ((Region.br 0 t).bindBranchArguments.lsubst (fun _ => r)) (r.substVars (Tm.singleSubst c)) L at step
  rw [lsubst_bindBranchArguments_br] at step
  exact step

theorem returnOnce_eq_branch (h : Normalizes Γ t c D)
    (includeFusion : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L)
    (seq : ConstructorSequencing Seed) :
    Paper.Extension.Eqv Seed Γ (returnOnce t) (.br 0 c) [D] := by
  induction h with
  | value hc =>
    exact .paper (.cfgEta (.native (.letValue hc (.br (ℓ := 0) rfl (.var (i := 0) rfl)))))
  | @let₁ Γ a b c d A D ha hb ia ib =>
    let fuse := Step.fuse ha.typed.1 hb.typed.1
    exact ((Paper.Extension.Eqv.extra fuse.typed.1 fuse.typed.2 (includeFusion fuse)).symm.trans
      (.let₁ ha.typed.1 ib)).trans
      (bind_eq_subst ia ha.typed.1 ha.typed.2 (.br (ℓ := 0) rfl hb.typed.2.hasType))
  | @pair Γ a b c d A B ha hb ia ib =>
    have right := ib.renameVars (Ren.wk Γ A)
    have rightVal : Tm.BranchValue (A :: Γ) (d.rename Nat.succ) B := by
      rw [Tm.rename_eq_subst]
      exact hb.typed.2.subst (fun _ _ hi => .var (Ren.wk Γ A hi))
    have rightEq :
        Paper.Extension.Eqv Seed (A :: Γ)
          (.let₁ (b.rename Nat.succ) (.br 0 (.pair (.var 1) (.var 0))))
          (.br 0 (.pair (.var 0) (d.rename Nat.succ))) [product A B] :=
      bind_eq_subst right (hb.typed.1.rename (Ren.wk Γ A)) rightVal
        (.br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))
    have last :=
      bind_eq_subst ia ha.typed.1 ha.typed.2
        (.br (ℓ := 0) (L := [product A B]) rfl (.pair (.var (i := 0) rfl) rightVal.hasType))
    have recover : (d.rename Nat.succ).subst (Tm.singleSubst c) = d := by
      rw [Tm.subst_rename]
      exact Tm.subst_var d
    have last' : Paper.Extension.Eqv Seed Γ
        (.let₁ a (.br 0 (.pair (.var 0) (d.rename Nat.succ)))) (.br 0 (.pair c d)) [product A B] := by
      simpa only [substVars, Tm.subst, Tm.singleSubst, Tm.consSubst, recover] using last
    exact (seq.pair ha hb).trans ((Paper.Extension.Eqv.let₁ ha.typed.1 rightEq).trans last')
  | inl ha ia =>
    exact (seq.inl ha).trans
      (bind_eq_subst ia ha.typed.1 ha.typed.2 (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl))))
  | inr ha ia =>
    exact (seq.inr ha).trans
      (bind_eq_subst ia ha.typed.1 ha.typed.2 (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl))))

theorem iterate_map_uniformity (h : Normalizes [A] t c D)
    (includeFusion : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L)
    (seq : ConstructorSequencing Seed)
    {f f₀ : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A}
    {g g₀ : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType D}
    (hf : (Paper.Extension.Singleton.projection Seed).map f = (Paper.Extension.Singleton.projection Seed).map f₀)
    (hg : (Paper.Extension.Singleton.projection Seed).map g = (Paper.Extension.Singleton.projection Seed).map g₀)
    (comm : f₀ ≫ coprod.map (𝟙 (ofType B)) (ofRegion (.br (ℓ := 0) rfl h.typed.2)) =
      ofRegion (.br (ℓ := 0) rfl h.typed.2) ≫ g₀) :
    (Paper.Extension.Singleton.projection Seed).map (iterate f) =
      (Paper.Extension.Singleton.projection Seed).map (boundReturn h.typed.1) ≫
        (Paper.Extension.Singleton.projection Seed).map (iterate g) := by
  have update := (Paper.Extension.Singleton.ofRegion_eq_iff Seed (returnOnce_typed h.typed.1)
    (.br (ℓ := 0) rfl h.typed.2)).2 (returnOnce_eq_branch h includeFusion seq)
  have uniform := iterate_uniformity_ofBranchValue h.typed.2 f₀ g₀ comm
  rw [Paper.Extension.Singleton.iterate_map_congr Seed hf, uniform, Functor.map_comp,
    ← Paper.Extension.Singleton.iterate_map_congr Seed hg]
  exact congrArg (fun x => x ≫ (Paper.Extension.Singleton.projection Seed).map (iterate g)) update.symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Constructors

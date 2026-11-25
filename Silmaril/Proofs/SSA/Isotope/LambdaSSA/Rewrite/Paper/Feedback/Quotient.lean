module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Feedback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Iteration.Thms

/-! # Iteration laws on guarded continuation classes -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open ContinuationContext (single)
open CategoryTheory

set_option backward.isDefEq.respectTransparency false

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {X Y Z : ContinuationContext Φ Γ}

private theorem fromCfgEta_feedback
    (f : CfgEta.fromNative.obj X ⟶ CfgEta.fromNative.obj (X.append Y)) :
    feedback (X := X) (Y := Y) (fromCfgEta.map f) = fromCfgEta.map (CfgEta.feedback f) :=
  Quotient.inductionOn f (fun _ => rfl)

private theorem fromCfgEta_prepend (X : ContinuationContext Φ Γ)
    (g : CfgEta.fromNative.obj Y ⟶ CfgEta.fromNative.obj Z) :
    prepend X (fromCfgEta.map g) = fromCfgEta.map (CfgEta.prepend X g) :=
  Quotient.inductionOn g (fun _ => rfl)

theorem feedback_postcompose
    (f : fromNative.obj X ⟶ fromNative.obj (X.append Y))
    (g : fromNative.obj Y ⟶ fromNative.obj Z) :
    feedback (X := X) (Y := Y) f ≫ g =
      feedback (X := X) (Y := Z) (f ≫ prepend X g) := by
  let F := fromCfgEta (Φ := Φ) (Γ := Γ)
  obtain ⟨f₀, hf⟩ := F.map_surjective (X := CfgEta.fromNative.obj X)
    (Y := CfgEta.fromNative.obj (X.append Y)) f
  obtain ⟨g₀, hg⟩ := F.map_surjective (X := CfgEta.fromNative.obj Y) (Y := CfgEta.fromNative.obj Z) g
  rw [← hf, ← hg]
  simpa only [F, fromNative, Functor.comp_obj, Functor.map_comp, ← fromCfgEta_feedback, ← fromCfgEta_prepend] using
    congrArg F.map (CfgEta.feedback_postcompose f₀ g₀)

theorem exists_singletonArrow {A : τ} (f : fromNative.obj (single A) ⟶ fromNative.obj Y) :
    ∃ (p : Region Φ) (hp : ValueBranches (A :: Γ) p Y.labels), singletonArrow hp = f := by
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep f
  have hp : ValueBranches (A :: Γ) (σ.val 0) Y.labels := σ.property (ℓ := 0) (A := A) rfl
  refine ⟨_, hp, toHom_eq_iff.mpr ?_⟩
  intro i D hi
  change At [A] i D at hi
  cases i with
  | zero => cases Option.some.inj hi; exact .refl hp.hasType
  | succ i => simp [At] at hi

theorem feedback_codiagonal (A : τ) (Y : ContinuationContext Φ Γ)
    (f : fromNative.obj (single A) ⟶ fromNative.obj ((single A).append ((single A).append Y))) :
    feedback (X := single A) (Y := Y)
      (feedback (X := single A) (Y := (single A).append Y) f) =
    feedback (X := single A) (Y := Y) (f ≫ collapseLabels A Y) := by
  obtain ⟨p, hp, rfl⟩ := exists_singletonArrow f
  apply toHom_eq_iff.mpr
  intro i D hi
  change At [A] i D at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    change Eqv (A :: Γ)
      (feedbackRegion [A] (feedbackRegion [A] (fun _ => p)) 0)
      (feedbackRegion [A] (fun _ => p.lsubst (labelId ∘ Nat.pred)) 0) Y.labels
    rw [← renameLabels_eq_lsubst]
    exact Paper.feedback_collapse hp
  | succ i => simp [At] at hi

theorem feedback_uniformity {A D : τ} {a : Tm Φ} (Y : ContinuationContext Φ Γ)
    (ha : Tm.BranchValue (A :: Γ) a D)
    (f : fromNative.obj (single A) ⟶ fromNative.obj ((single A).append Y))
    (g : fromNative.obj (single D) ⟶ fromNative.obj ((single D).append Y))
    (square : f ≫ localStateChange Y ha = stateChange ha ≫ g) :
    feedback (X := single A) (Y := Y) f =
      stateChange ha ≫ feedback (X := single D) (Y := Y) g := by
  obtain ⟨p, hp, rfl⟩ := exists_singletonArrow f
  obtain ⟨q, hq, rfl⟩ := exists_singletonArrow g
  have hs := (toHom_eq_iff.mp square) (i := 0) (A := A) rfl
  change Eqv (A :: Γ) (p.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a)))
    ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => q))) (D :: Y.labels) at hs
  apply toHom_eq_iff.mpr
  intro i T hi
  change At [A] i T at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    change Eqv (A :: Γ) (feedbackRegion [A] (fun _ => p) 0)
      ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => feedbackRegion [D] (fun _ => q) 0))) Y.labels
    exact Paper.feedback_uniform hp hq.hasType ha hs
  | succ i => simp [At] at hi

theorem collapseLabels_left (A : τ) (Y : ContinuationContext Φ Γ) :
    fromNative.map ((single A).appendInl ((single A).append Y)) ≫ collapseLabels A Y =
      fromNative.map ((single A).appendInl Y) := by
  apply toHom_eq_iff.mpr
  intro i D hi
  change At [A] i D at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    change Eqv (A :: Γ) (compLSubst labelId (labelId ∘ Nat.pred) 0) (labelId 0) (A :: Y.labels)
    rw [compLSubst_id_left]
    exact .refl (.br rfl (.var rfl))
  | succ i => simp [At] at hi

theorem collapseLabels_right (A : τ) (Y : ContinuationContext Φ Γ) :
    fromNative.map ((single A).appendInr ((single A).append Y)) ≫ collapseLabels A Y =
      𝟙 (fromNative.obj ((single A).append Y)) := by
  apply toHom_eq_iff.mpr
  intro i D hi
  change At (A :: Y.labels) i D at hi
  change Eqv (D :: Γ) (compLSubst labelId (labelId ∘ Nat.pred) (1 + i))
    (labelId i) (A :: Y.labels)
  rw [compLSubst_id_left, Function.comp_apply, Nat.one_add, Nat.pred_succ]
  exact .refl (.br hi (.var rfl))

theorem localStateChange_left (Y : ContinuationContext Φ Γ)
    {A D : τ} {a : Tm Φ} (ha : Tm.BranchValue (A :: Γ) a D) :
    fromNative.map ((single A).appendInl Y) ≫ localStateChange Y ha =
      stateChange ha ≫ fromNative.map ((single D).appendInl Y) := by
  apply toHom_eq_iff.mpr
  intro i T hi
  change At [A] i T at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    change Eqv (A :: Γ) (compLSubst labelId (CfgEta.Uniformity.localMap a) 0)
      (compLSubst (fun _ => .br 0 a) labelId 0) (D :: Y.labels)
    rw [compLSubst_id_left, compLSubst_id_right]
    exact .refl (.br rfl ha.hasType)
  | succ i => simp [At] at hi

theorem localStateChange_right (Y : ContinuationContext Φ Γ)
    {A D : τ} {a : Tm Φ} (ha : Tm.BranchValue (A :: Γ) a D) :
    fromNative.map ((single A).appendInr Y) ≫ localStateChange Y ha =
      fromNative.map ((single D).appendInr Y) := by
  apply toHom_eq_iff.mpr
  intro i T hi
  change At Y.labels i T at hi
  change Eqv (T :: Γ) (compLSubst labelId (CfgEta.Uniformity.localMap a) (1 + i))
    (labelId (1 + i)) (D :: Y.labels)
  rw [compLSubst_id_left, Nat.one_add]
  exact .refl (.br (show At (D :: Y.labels) (i + 1) T from hi) (.var (i := 0) rfl))

theorem appendInl_prepend (X : ContinuationContext Φ Γ)
    (g : fromNative.obj Y ⟶ fromNative.obj Z) :
    fromNative.map (X.appendInl Y) ≫ prepend X g = fromNative.map (X.appendInl Z) := by
  let F := fromCfgEta (Φ := Φ) (Γ := Γ)
  obtain ⟨g₀, hg⟩ := F.map_surjective (X := CfgEta.fromNative.obj Y) (Y := CfgEta.fromNative.obj Z) g
  rw [← hg]
  simpa only [F, fromNative, Functor.comp_obj, Functor.comp_map, Functor.map_comp, ← fromCfgEta_prepend]
    using congrArg F.map (CfgEta.appendInl_prepend X g₀)

theorem appendInr_prepend (X : ContinuationContext Φ Γ)
    (g : fromNative.obj Y ⟶ fromNative.obj Z) :
    fromNative.map (X.appendInr Y) ≫ prepend X g = g ≫ fromNative.map (X.appendInr Z) := by
  let F := fromCfgEta (Φ := Φ) (Γ := Γ)
  obtain ⟨g₀, hg⟩ := F.map_surjective (X := CfgEta.fromNative.obj Y) (Y := CfgEta.fromNative.obj Z) g
  rw [← hg]
  simpa only [F, fromNative, Functor.comp_obj, Functor.comp_map, Functor.map_comp, ← fromCfgEta_prepend]
    using congrArg F.map (CfgEta.appendInr_prepend X g₀)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

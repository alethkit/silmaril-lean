module

public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Equations

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs

open Expr

variable {τ : Type u} {Φ : Type v} {ε : Type w}

private theorem project_subst (i : Nat) (a : Expr Φ) (σ : Nat → Expr Φ) :
    (project i a).subst σ = project i (a.subst σ) := by
  induction i generalizing a with
  | zero => rfl
  | succ i ih => exact ih (first a)

private theorem project_wk (i : Nat) (a : Expr Φ) (ρ : Nat → Nat) :
    (project i a).wk ρ = project i (a.wk ρ) := by
  induction i generalizing a with
  | zero => rfl
  | succ i ih => exact ih (first a)

private theorem liftProj :
    liftSubst (fun i => project i (.var 0 : Expr Φ)) =
      (fun | 0 => .var 0 | i + 1 => project i (.var 1)) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact project_wk i (.var 0) Nat.succ

private theorem liftProj₂ :
    liftSubst (liftSubst (fun i => project i (.var 0 : Expr Φ))) =
      (fun
        | 0 => .var 0
        | i + 1 => match i with
          | 0 => .var 1
          | j + 1 => project j (.var 2)) := by
  rw [liftProj]
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i => exact project_wk i (.var 1) Nat.succ

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]

private theorem var₀ {Γ : EffectCtx τ ε} {A : τ} {e : ε} :
    Wf ((A, ⊥) :: Γ) (.var 0 : Expr Φ) A e :=
  .var 0 bot_le

private theorem var₁ {Γ : EffectCtx τ ε} {A : τ} {e : ε} (slot : τ × ε) :
    Wf (slot :: (A, ⊥) :: Γ) (.var 1 : Expr Φ) A e :=
  .var ⟨1, by simp⟩ bot_le

private theorem var₂ {Γ : EffectCtx τ ε} {A : τ} {e : ε} (older newer : τ × ε) :
    Wf (newer :: older :: (A, ⊥) :: Γ) (.var 2 : Expr Φ) A e :=
  .var ⟨2, by simp⟩ bot_le

private theorem project_congr (Γ : EffectCtx τ ε) (i : Fin Γ.length)
    {Δ : EffectCtx τ ε} {a b : Expr Φ} {e : ε}
    (h : Eqv Δ (packType Γ) e a b) :
    Eqv Δ (Γ.get i).1 e (project i.val a) (project i.val b) := by
  induction Γ generalizing a b with
  | nil => exact i.elim0
  | cons slot Γ ih =>
    obtain ⟨A, _⟩ := slot
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .let2 h (.refl var₀)
    · exact ih j (.let2 h (.refl (var₁ _)))

theorem project_wf (Γ : EffectCtx τ ε) (i : Fin Γ.length)
    {Δ : EffectCtx τ ε} {a : Expr Φ} {e : ε} (h : Wf Δ a (packType Γ) e) :
    Wf Δ (project i.val a) (Γ.get i).1 e :=
  (eqv_typed (project_congr Γ i (.refl h))).1

private theorem tuple_wf (Γ : EffectCtx τ ε) {Δ : EffectCtx τ ε} {e : ε}
    {σ : Nat → Expr Φ} (h : ∀ i : Fin Γ.length, Wf Δ (σ i.val) (Γ.get i).1 e) :
    Wf Δ (tuple Γ.length σ) (packType Γ) e := by
  induction Γ generalizing σ with
  | nil => exact .unit Δ e
  | cons _ Γ ih => exact .pair (ih (fun i => h i.succ)) (h 0)

private theorem first_pair {Γ : EffectCtx τ ε} {A B : τ} {a b : Expr Φ}
    (ha : Wf Γ a A ⊥) (hb : Wf Γ b B ⊥) :
    Eqv Γ A ⊥ (first (.pair a b)) a := by
  have hb' : Wf ((A, ⊥) :: Γ) b.wk0 B ⊥ := wf_wk hb (Renaming.wk0 Γ _)
  have hvar : Wf ((B, ⊥) :: (A, ⊥) :: Γ) (.var 1 : Expr Φ) A ⊥ := var₁ _
  exact (Eqv.step (.rewrite (.let₂ (.pair ha hb) hvar)
      (.let₁ ha (.let₁ hb' hvar)) (.let2_pair _ _ _))).trans
    ((Eqv.let1 (.refl ha) (.step (.let1_beta hb' hvar))).trans
      (.step (.rewrite (.let₁ ha var₀) ha (.let1_eta _))))

private theorem second_pair {Γ : EffectCtx τ ε} {A B : τ} {a b : Expr Φ}
    (ha : Wf Γ a A ⊥) (hb : Wf Γ b B ⊥) :
    Eqv Γ B ⊥ (second (.pair a b)) b := by
  have hb' : Wf ((A, ⊥) :: Γ) b.wk0 B ⊥ := wf_wk hb (Renaming.wk0 Γ _)
  have hvar : Wf ((B, ⊥) :: (A, ⊥) :: Γ) (.var 0 : Expr Φ) B ⊥ := var₀
  have drop : Eqv Γ B ⊥ (.let₁ a b.wk0) b := by
    simpa only [subst0_wk0] using Eqv.step (Step.let1_beta ha hb')
  exact (Eqv.step (.rewrite (.let₂ (.pair ha hb) hvar)
      (.let₁ ha (.let₁ hb' hvar)) (.let2_pair _ _ _))).trans
    ((Eqv.let1 (.refl ha) (.step (.rewrite (.let₁ hb' hvar) hb' (.let1_eta _)))).trans drop)

private theorem project_tuple (Γ : EffectCtx τ ε) {Δ : EffectCtx τ ε}
    {σ : Nat → Expr Φ} (h : ∀ i : Fin Γ.length, Wf Δ (σ i.val) (Γ.get i).1 ⊥)
    (i : Fin Γ.length) :
    Eqv Δ (Γ.get i).1 ⊥ (project i.val (tuple Γ.length σ)) (σ i.val) := by
  induction Γ generalizing σ with
  | nil => exact i.elim0
  | cons _ Γ ih =>
    have hTail := tuple_wf Γ (σ := σ ∘ Nat.succ) (fun i => h i.succ)
    have hHead := h 0
    refine Fin.cases ?_ (fun j => ?_) i
    · exact second_pair hTail hHead
    · exact (project_congr Γ j (first_pair hTail hHead)).trans (ih (σ := σ ∘ Nat.succ) (fun i => h i.succ) j)

private theorem packingSubst (Γ : EffectCtx τ ε) :
    TypedSubst [(packType Γ, ⊥)] Γ (fun i => project i (.var 0 : Expr Φ)) :=
  fun i => project_wf Γ i var₀

theorem oneSubst {Γ : EffectCtx τ ε} {A : τ} {a : Expr Φ} (h : Wf Γ a A ⊥) :
    TypedSubst Γ [(A, ⊥)] a.subst0 := by
  intro i
  exact Fin.cases h (fun j => j.elim0) i

theorem pack_wf {Γ : EffectCtx τ ε} {a : Expr Φ} {A : τ} {e : ε} (h : Wf Γ a A e) :
    Wf [(packType Γ, ⊥)] (packExpr a) A e :=
  wf_subst h (packingSubst Γ)

theorem pack_eqv {Γ : EffectCtx τ ε} {a b : Expr Φ} {A : τ} {e : ε}
    (h : Eqv Γ A e a b) : Eqv [(packType Γ, ⊥)] A e (packExpr a) (packExpr b) :=
  eqv_subst h (packingSubst Γ)

private theorem tuple_vars {Γ : EffectCtx τ ε} (hp : Γ.Pure) (i : Fin Γ.length) :
    Wf Γ (.var i.val : Expr Φ) (Γ.get i).1 ⊥ :=
  .var i (hp i).le

theorem unpack_wf {Γ : EffectCtx τ ε} {a : Expr Φ} {A : τ} {e : ε}
    (hp : Γ.Pure) (h : Wf [(packType Γ, ⊥)] a A e) : Wf Γ (unpackExpr Γ a) A e :=
  wf_subst h (oneSubst (tuple_wf Γ (tuple_vars hp)))

theorem unpack_eqv {Γ : EffectCtx τ ε} {a b : Expr Φ} {A : τ} {e : ε}
    (hp : Γ.Pure) (h : Eqv [(packType Γ, ⊥)] A e a b) :
    Eqv Γ A e (unpackExpr Γ a) (unpackExpr Γ b) :=
  eqv_subst h (oneSubst (tuple_wf Γ (tuple_vars hp)))

theorem unpack_pack {Γ : EffectCtx τ ε} {a : Expr Φ} {A : τ} {e : ε}
    (hp : Γ.Pure) (ha : Wf Γ a A e) : Eqv Γ A e (unpackExpr Γ (packExpr a)) a := by
  have related : RelatedSubst (Φ := Φ) Γ Γ
      (fun i => (project i (.var 0)).subst (tuple Γ.length Expr.var).subst0)
      Expr.var := by
    intro i
    change Eqv Γ (Γ.get i).1 (Γ.get i).2 ((project i.val (.var 0)).subst _) (.var i.val)
    rw [project_subst, hp i]
    exact project_tuple Γ (tuple_vars hp) i
  simpa only [unpackExpr, packExpr, subst_subst, subst_var] using eqv_subst_congr ha related

private theorem tuple_subst (n : Nat) (σ θ : Nat → Expr Φ) :
    (tuple n σ).subst θ = tuple n (fun i => (σ i).subst θ) := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih => simp only [tuple, Expr.subst, ih]; rfl

private theorem pair_first_second {Γ : EffectCtx τ ε} {A B : τ} {a : Expr Φ}
    (h : Wf Γ a (product A B) ⊥) :
    Eqv Γ (product A B) ⊥ (.pair (first a) (second a)) a := by
  let P := product A B
  let body : Expr Φ := .pair (first (.var 0)) (second (.var 0))
  have bodyWf (Δ : EffectCtx τ ε) : Wf ((P, ⊥) :: Δ) body P ⊥ :=
    .pair (.let₂ var₀ (var₁ _)) (.let₂ var₀ var₀)
  let vs : Expr Φ := .pair (.var 1) (.var 0)
  have vsWf : Wf ((B, ⊥) :: (A, ⊥) :: Γ) vs P ⊥ := .pair (var₁ _) var₀
  have eta : Eqv Γ P ⊥ (.let₂ a vs) a :=
    .step (.rewrite (.let₂ h vsWf) h (.let2_eta _))
  have beta : Eqv Γ P ⊥ (.let₁ a body) (.pair (first a) (second a)) :=
    .step (.let1_beta h (bodyWf Γ))
  have commute : Eqv Γ P ⊥ (.let₁ (.let₂ a vs) body) (.let₂ a (.let₁ vs body)) :=
    .step (.rewrite (.let₁ (.let₂ h vsWf) (bodyWf Γ))
      (.let₂ h (.let₁ vsWf (bodyWf _))) (.let1_let2 _ _ _))
  have betaPair : Eqv ((B, ⊥) :: (A, ⊥) :: Γ) P ⊥ (.let₁ vs body)
      (.pair (first vs) (second vs)) :=
    .step (.let1_beta vsWf (bodyWf _))
  have projections : Eqv ((B, ⊥) :: (A, ⊥) :: Γ) P ⊥
      (.pair (first vs) (second vs)) vs :=
    .pair (first_pair (var₁ _) var₀) (second_pair (var₁ _) var₀)
  exact beta.symm.trans ((Eqv.let1 eta.symm (.refl (bodyWf Γ))).trans
    (commute.trans ((Eqv.let2 (.refl h) (betaPair.trans projections)).trans eta)))

private theorem tuple_project (Γ : EffectCtx τ ε) {Δ : EffectCtx τ ε} {a : Expr Φ}
    (h : Wf Δ a (packType Γ) ⊥) :
    Eqv Δ (packType Γ) ⊥ (tuple Γ.length (fun i => project i a)) a := by
  induction Γ generalizing a with
  | nil => exact .step (.terminal (.unit _ _) h)
  | cons slot Γ ih =>
    obtain ⟨A, _⟩ := slot
    have firstWf : Wf Δ (first a) (packType Γ) ⊥ := .let₂ h (var₁ _)
    have secondWf : Wf Δ (second a) A ⊥ := .let₂ h var₀
    exact (Eqv.pair (ih firstWf) (.refl secondWf)).trans (pair_first_second h)

theorem pack_unpack {Γ : EffectCtx τ ε} {a : Expr Φ} {A : τ} {e : ε}
    (ha : Wf [(packType Γ, ⊥)] a A e) :
    Eqv [(packType Γ, ⊥)] A e (packExpr (unpackExpr Γ a)) a := by
  have related : RelatedSubst (Φ := Φ) (ε := ε) [(packType Γ, ⊥)] [(packType Γ, ⊥)]
      (fun i => (((tuple Γ.length Expr.var).subst0 i).subst (fun j => project j (.var 0))))
      Expr.var := by
    intro i
    refine Fin.cases ?_ (fun j => j.elim0) i
    change Eqv _ (packType Γ) (⊥ : ε)
      ((tuple Γ.length Expr.var).subst (fun j => project j (.var 0))) (.var 0)
    rw [tuple_subst]
    exact tuple_project Γ (var₀ (Γ := []) (A := packType Γ))
  simpa only [packExpr, unpackExpr, subst_subst, subst_var] using eqv_subst_congr ha related

private theorem extendProj {Γ Δ : EffectCtx τ ε} {A : τ} {x y : Expr Φ} {σ : Nat → Expr Φ}
    (hx : Wf Δ x (packType Γ) ⊥) (hy : Wf Δ y A ⊥)
    (h : RelatedSubst Δ Γ (fun i => project i x) σ) :
    RelatedSubst Δ ((A, ⊥) :: Γ) (fun i => project i (.pair x y))
      (fun | 0 => y | i + 1 => σ i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact second_pair hx hy
  · exact (project_congr Γ j (eqv_wkEff (first_pair hx hy) bot_le)).trans (h j)

private theorem binderSubst (Γ : EffectCtx τ ε) (A : τ) :
    RelatedSubst [(A, ⊥), (packType Γ, ⊥)] ((A, ⊥) :: Γ)
      (fun i => project i (.pair (.var 1) (.var 0) : Expr Φ))
      (liftSubst (fun i => project i (.var 0))) := by
  rw [liftProj]
  exact extendProj (var₁ _) var₀ (fun i => .refl (project_wf Γ i (var₁ _)))

private theorem binderSubst₂ (Γ : EffectCtx τ ε) (A B : τ) :
    RelatedSubst [(B, ⊥), (A, ⊥), (packType Γ, ⊥)] ((B, ⊥) :: (A, ⊥) :: Γ)
      (fun i => project i (.pair (.pair (.var 2) (.var 1)) (.var 0) : Expr Φ))
      (liftSubst (liftSubst (fun i => project i (.var 0)))) := by
  rw [liftProj₂]
  have hx : Wf ([(B, ⊥), (A, ⊥), (packType Γ, ⊥)] : EffectCtx τ ε) (.var 2 : Expr Φ) (packType Γ) ⊥ :=
    var₂ _ _
  have hy : Wf ([(B, ⊥), (A, ⊥), (packType Γ, ⊥)] : EffectCtx τ ε) (.var 1 : Expr Φ) A ⊥ := var₁ _
  exact extendProj (.pair hx hy) var₀ (extendProj (σ := fun i => project i (.var 2)) hx hy (fun i =>
    .refl (project_wf Γ i (wf_wkEff hx bot_le))))

private theorem denoteBinder {Γ : EffectCtx τ ε} {a : Expr Φ} {A B : τ} {e : ε}
    (h : Wf ((A, ⊥) :: Γ) a B e)
    (ih : Eqv [(packType ((A, ⊥) :: Γ), ⊥)] B e (denoteExpr a) (packExpr a)) :
    Eqv [(A, ⊥), (packType Γ, ⊥)] B e
      ((denoteExpr a).subst (Expr.pair (.var 1) (.var 0)).subst0)
      (a.subst (liftSubst (fun i => project i (.var 0)))) := by
  refine (eqv_subst ih (oneSubst (.pair (var₁ _) var₀))).trans ?_
  simpa only [packExpr, subst_subst, project_subst, Expr.subst, Expr.subst0] using eqv_subst_congr h (binderSubst Γ A)

private theorem denoteBinder₂ {Γ : EffectCtx τ ε} {a : Expr Φ} {A B C : τ} {e : ε}
    (h : Wf ((B, ⊥) :: (A, ⊥) :: Γ) a C e)
    (ih : Eqv [(packType ((B, ⊥) :: (A, ⊥) :: Γ), ⊥)] C e (denoteExpr a) (packExpr a)) :
    Eqv [(B, ⊥), (A, ⊥), (packType Γ, ⊥)] C e
      ((denoteExpr a).subst (Expr.pair (.pair (.var 2) (.var 1)) (.var 0)).subst0)
      (a.subst (liftSubst (liftSubst (fun i => project i (.var 0))))) := by
  refine (eqv_subst ih (oneSubst (.pair (.pair (var₂ _ _) (var₁ _)) var₀))).trans ?_
  simpa only [packExpr, subst_subst, project_subst, Expr.subst, Expr.subst0] using eqv_subst_congr h (binderSubst₂ Γ A B)

theorem denote_eqv_pack {Γ : EffectCtx τ ε} {a : Expr Φ} {A : τ} {e : ε}
    (h : Wf Γ a A e) : Eqv [(packType Γ, ⊥)] A e (denoteExpr a) (packExpr a) := by
  induction h with
  | var i he => exact .refl (project_wf _ i var₀)
  | op hf _ ih => exact .op hf ih
  | let₁ _ hb ihA ihB => exact .let1 ihA (denoteBinder hb ihB)
  | pair _ _ ihA ihB => exact .pair ihA ihB
  | unit => exact .refl (.unit _ _)
  | let₂ _ hb ihA ihB => exact .let2 ihA (denoteBinder₂ hb ihB)
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ hl hr ihA ihL ihR => exact .case ihA (denoteBinder hl ihL) (denoteBinder hr ihR)
  | abort _ ih => exact .abort ih

end Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs

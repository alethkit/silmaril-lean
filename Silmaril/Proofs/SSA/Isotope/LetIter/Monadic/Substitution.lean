module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Defs
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Monadic

open Silmaril.Isotope Silmaril.Isotope.Semantics

namespace Silmaril.Isotope.LetIter.LocallyNameless.Derivation.Proofs

universe u v w q

variable {τ : Type u} [TypeFormers τ] (D : τ → Type v)
  [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
  {m : Type v → Type v} [Monad m] [Elgot.Iterate m] (M : InstructionModel D Φ m)
  {Γ : Ctx ν τ} {n k : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ k}
  {t : Tm ν Φ n} {A : τ} (γ : FreeEnv D Γ)

private theorem denote_cast_bv (i : Fin k) (h : δ.get i = A)
    (ρ : BoundEnv D δ) :
    (h ▸ (Derivation.bv (ι := i)) : Derivation Φ Γ δ (.bv i) A).denote D M γ ρ =
      pure (cast (congrArg D h) (ρ i)) := by
  subst A
  rfl

omit [TypeFormers τ] [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D] in
private theorem up_agree (r : TypedRenaming β δ) {ρ : BoundEnv D β} {ξ : BoundEnv D δ}
    (h : ∀ i, HEq (ξ (r.toFun i)) (ρ i)) {B : τ} (x : D B) :
    ∀ i, HEq ((ξ.snoc x) ((TypedRenaming.up r B).toFun i)) ((ρ.snoc x) i) :=
  fun i => Fin.cases HEq.rfl (fun j => h j) i

set_option backward.isDefEq.respectTransparency false in
public theorem denote_rename (d : Derivation Φ Γ β t A) (r : TypedRenaming β δ)
    (ρ : BoundEnv D β) (ξ : BoundEnv D δ) (hr : ∀ i, HEq (ξ (r.toFun i)) (ρ i)) :
    (d.rename r).denote D M γ ξ = d.denote D M γ ρ := by
  induction d generalizing k with
  | fv _ | unit => rfl
  | @bv n β i =>
    rw [Derivation.rename]
    exact (denote_cast_bv D M γ (r.toFun i) (r.typed i) ξ).trans
      (congrArg pure (eq_of_heq ((cast_heq _ _).trans (hr i))))
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [Derivation.rename, Derivation.denote]
    rw [ih r ρ ξ hr]
  | pair _ _ ihL ihR =>
    simp only [Derivation.rename, Derivation.denote]
    rw [ihL r ρ ξ hr, ihR r ρ ξ hr]
  | let₁ _ _ ihA ihB =>
    simp only [Derivation.rename, Derivation.denote]
    rw [ihA r ρ ξ hr]
    apply bind_congr
    intro x
    exact ihB _ _ _ (up_agree D r hr x)
  | let₂ _ _ ihA ihB =>
    simp only [Derivation.rename, Derivation.denote]
    rw [ihA r ρ ξ hr]
    apply bind_congr
    intro p
    exact ihB _ _ _ (up_agree D _ (up_agree D r hr _) _)
  | case _ _ _ ihA ihL ihR =>
    simp only [Derivation.rename, Derivation.denote]
    rw [ihA r ρ ξ hr]
    apply bind_congr
    intro v
    cases CoproductModel.coprodEquiv (D := D) _ _ v with
    | inl x => exact ihL _ _ _ (up_agree D r hr x)
    | inr y => exact ihR _ _ _ (up_agree D r hr y)
  | iter _ _ ihA ihB =>
    simp only [Derivation.rename, Derivation.denote]
    rw [ihA r ρ ξ hr]
    congr 2
    funext x
    rw [ihB _ _ _ (up_agree D r hr x)]

set_option backward.isDefEq.respectTransparency false in
private theorem up_subst {σ : Fin n → Tm ν Φ k} (s : DerivSubst (Γ := Γ) β δ σ)
    (ρ : BoundEnv D β) (ξ : BoundEnv D δ)
    (hs : ∀ i, (s i).denote D M γ ξ = pure (ρ i)) {B : τ} (x : D B) :
    ∀ i, ((s.up B) i).denote D M γ (ξ.snoc x) = pure ((ρ.snoc x) i) := by
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  exact (denote_rename D M γ (s j) (TypedRenaming.succ δ B) ξ (ξ.snoc x)
    (fun _ => HEq.rfl)).trans (hs j)

set_option backward.isDefEq.respectTransparency false in
public theorem denote_bsubst (d : Derivation Φ Γ β t A) {σ : Fin n → Tm ν Φ k}
    (s : DerivSubst (Γ := Γ) β δ σ) (ρ : BoundEnv D β) (ξ : BoundEnv D δ)
    (hs : ∀ i, (s i).denote D M γ ξ = pure (ρ i)) :
    (d.bsubst s).denote D M γ ξ = d.denote D M γ ρ := by
  induction d generalizing k with
  | fv _ | unit => rfl
  | bv => exact hs _
  | op _ ih | inl _ ih | inr _ ih | abort _ ih =>
    simp only [Derivation.bsubst, Derivation.denote]
    rw [ih s ρ ξ hs]
  | pair _ _ ihL ihR =>
    simp only [Derivation.bsubst, Derivation.denote]
    rw [ihL s ρ ξ hs, ihR s ρ ξ hs]
  | let₁ _ _ ihA ihB =>
    simp only [Derivation.bsubst, Derivation.denote]
    rw [ihA s ρ ξ hs]
    apply bind_congr
    intro x
    exact ihB _ _ _ (up_subst D M γ s ρ ξ hs x)
  | let₂ _ _ ihA ihB =>
    simp only [Derivation.bsubst, Derivation.denote]
    rw [ihA s ρ ξ hs]
    apply bind_congr
    intro p
    exact ihB _ _ _ (up_subst D M γ _ _ _ (up_subst D M γ s ρ ξ hs _) _)
  | case _ _ _ ihA ihL ihR =>
    simp only [Derivation.bsubst, Derivation.denote]
    rw [ihA s ρ ξ hs]
    apply bind_congr
    intro v
    cases CoproductModel.coprodEquiv (D := D) _ _ v with
    | inl x => exact ihL _ _ _ (up_subst D M γ s ρ ξ hs x)
    | inr y => exact ihR _ _ _ (up_subst D M γ s ρ ξ hs y)
  | iter _ _ ihA ihB =>
    simp only [Derivation.bsubst, Derivation.denote]
    rw [ihA s ρ ξ hs]
    congr 2
    funext x
    rw [ihB _ _ _ (up_subst D M γ s ρ ξ hs x)]

end Silmaril.Isotope.LetIter.LocallyNameless.Derivation.Proofs

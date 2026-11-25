module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Bind.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

/-! # Correctness of substitution and binding in normalized sequences -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.BindProofs

universe u r

variable {α Φ : Type u} (S : Signature α Φ) {a c : α}

private theorem tuple_subst {k : Nat} (xs : Fin k → Expr Φ) (σ : Nat → Expr Φ) :
    (sourceTuple k xs).subst σ = sourceTuple k (fun i => (xs i).subst σ) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [sourceTuple, Expr.subst, ih]

variable {n m : Nat} {slots : Fin n → α} {target : Fin m → α}

private theorem tree_subst_source (p : Tree S slots c) (σ : TreeSubst S slots target)
    (ξ : Nat → Expr Φ) (h : ∀ i : Fin n, ξ i.val = (σ i).source) :
    (p.interpret S (Tree S target) Tree.op σ).source = p.source.subst ξ := by
  induction p with
  | var i => exact (h i).symm
  | op f args ih => simp only [Tree.interpret, Tree.source, Expr.subst, tuple_subst, ih]

private theorem tree_wk0_source (v : Tree S slots c) (x : α) :
    (v.interpret S (Tree S (extendSorts x slots)) Tree.op (fun j => .var j.succ)).source =
      v.source.wk0 := by
  rw [Expr.wk0, Expr.wk_eq_subst]
  exact tree_subst_source S v _ _ fun _ => rfl

public theorem subst_source (p : Sequence S c slots) (σ : TreeSubst S slots target)
    (ξ : Nat → Expr Φ) (h : ∀ i : Fin n, ξ i.val = (σ i).source) :
    (subst S p σ).source = p.source.subst ξ := by
  induction p generalizing m ξ with
  | ret p => exact tree_subst_source S p σ ξ h
  | @call k as f args next ih =>
    have h' (i : Fin (k + 1)) :
        Expr.liftSubst ξ i.val = (liftSubst S σ (S.out f) i).source := by
      refine Fin.cases rfl (fun j => ?_) i
      change (ξ j.val).wk0 =
        ((σ j).interpret S (Tree S (extendSorts (S.out f) target)) Tree.op
          (fun t => .var t.succ)).source
      rw [h j]
      exact (tree_wk0_source S (σ j) (S.out f)).symm
    simp only [Sequence.subst, Sequence.source, Tree.source, Expr.subst, tuple_subst,
      tree_subst_source S _ σ ξ h, ih _ _ h']

public theorem subst0_source (q : Sequence S c (extendSorts a slots)) (v : Tree S slots a) :
    (subst S q (subst0 S v)).source = q.source.subst v.source.subst0 := by
  exact subst_source S q _ _ fun i => Fin.cases rfl (fun _ => rfl) i

public theorem liftAmbient_source (q : Sequence S c (extendSorts a slots)) (x : α) :
    (subst S q (liftAmbientSubst S a x)).source = q.source.wk1 := by
  rw [Expr.wk1, Expr.wk_eq_subst]
  exact subst_source S q _ _ fun i => Fin.cases rfl (fun _ => rfl) i

public theorem weaken_source (p : Sequence S c slots) (x : α) :
    (weaken S x p).source = p.source.wk0 := by
  rw [Expr.wk0, Expr.wk_eq_subst]
  exact subst_source S p _ _ fun _ => rfl

section Typed

variable {ε : Type r} [HasEff Φ ε] [Preorder ε] [Bot ε]

omit [Preorder ε] in
private theorem tree_pure_subst (p : Tree S slots c) (hp : DeclaredPure (ε := ε) S p)
    (σ : TreeSubst S slots target) (hσ : ∀ i, DeclaredPure (ε := ε) S (σ i)) :
    DeclaredPure (ε := ε) S (p.interpret S (Tree S target) Tree.op σ) := by
  induction p with
  | var i => exact hσ i
  | op f args ih => exact ⟨hp.1, fun i => ih i (hp.2 i)⟩

public theorem subst_typed (e : ε) (p : Sequence S c slots) (hp : Sequence.WellTyped S e p)
    (σ : TreeSubst S slots target) (hσ : ∀ i, DeclaredPure (ε := ε) S (σ i)) :
    Sequence.WellTyped S e (subst S p σ) := by
  induction p generalizing m with
  | ret p => exact tree_pure_subst S p hp σ hσ
  | call f args next ih =>
    refine ⟨fun i => tree_pure_subst S (args i) (hp.1 i) σ hσ, hp.2.1, hp.2.2.1,
      ih hp.2.2.2 _ ?_⟩
    intro i
    refine Fin.cases (motive := fun j =>
      DeclaredPure (ε := ε) S (liftSubst S σ (S.out f) j)) trivial (fun j => ?_) i
    exact tree_pure_subst S (σ j) (hσ j) _ fun _ => trivial

public theorem weaken_typed (x : α) (e : ε) (p : Sequence S c slots) (hp : Sequence.WellTyped S e p) :
    Sequence.WellTyped S e (weaken S x p) :=
  subst_typed S e p hp _ (fun _ => trivial)

omit [Preorder ε] in
private theorem lifted_ambient_pure (a x : α) (i : Fin (n + 1)) :
    DeclaredPure (ε := ε) S (liftAmbientSubst S (slots := slots) a x i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact trivial
  · exact trivial

public theorem bind_typed (e : ε) (p : Sequence S a slots) (q : Sequence S c (extendSorts a slots))
    (hp : Sequence.WellTyped S e p) (hq : Sequence.WellTyped S e q) :
    Sequence.WellTyped S e (bind S p q) := by
  induction p with
  | ret v =>
    exact subst_typed S e q hq (subst0 S v)
      (fun i => Fin.cases (motive := fun j => DeclaredPure (ε := ε) S (subst0 S v j))
        hp (fun _ => trivial) i)
  | call f args next ih =>
    refine ⟨hp.1, hp.2.1, hp.2.2.1, ih _ hp.2.2.2
      (subst_typed S e q hq (liftAmbientSubst S a (S.out f)) (lifted_ambient_pure S a (S.out f)))⟩

end Typed

section Soundness

variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]

private theorem extended_pure {Γ : EffectCtx (Ty α) ε} (hΓ : Γ.Pure) (x : α) :
    EffectCtx.Pure ((Ty.base x, (⊥ : ε)) :: Γ) :=
  fun i => Fin.cases (motive := fun j => (((Ty.base x, (⊥ : ε)) :: Γ).get j).2 = ⊥)
    rfl hΓ i

private theorem extended_slots {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}
    (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (x : α) :
    ∀ i : Fin (Γ.length + 1),
      (((Ty.base x, (⊥ : ε)) :: Γ).get i).1 = .base (extendSorts x ts i) :=
  fun i => Fin.cases (motive := fun j =>
    (((Ty.base x, (⊥ : ε)) :: Γ).get j).1 = .base (extendSorts x ts j)) rfl hslots i

private theorem bind_eqv_aux (e : ε) (p : Sequence S a slots) (hp : Sequence.WellTyped S e p) :
    letI := S.endpoints
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n), Γ.Pure →
      (∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots (i.cast hlen))) →
      ∀ (q : Sequence S c (extendSorts a slots)), Sequence.WellTyped S e q →
      Eqv Γ (.base c) e (.let₁ p.source q.source) (bind S p q).source := by
  let instr := S.endpoints
  induction p with
  | @ret size ambient v =>
    intro Γ hlen hΓ hs q hq
    subst size
    change Eqv Γ (.base c) e (.let₁ v.source q.source) (subst S q (subst0 S v)).source
    rw [subst0_source S]
    exact .step (.let1_beta (tree_wf S v hp hΓ hs ⊥)
      (Sequence.wf S (extended_pure hΓ a) (extended_slots hs a) e q hq))
  | @call size ambient f args next ih =>
    intro Γ hlen hΓ hs q hq
    subst size
    let x := S.out f
    let p := Tree.op f args
    let q' := subst S q (liftAmbientSubst S a x)
    have hq' : Sequence.WellTyped S e q' :=
      subst_typed S e q hq _ (lifted_ambient_pure S a x)
    have hf := SingleCall.request_wf S args hp.1 hΓ hs hp.2.2.1
    have hΓx := extended_pure hΓ x
    have hsx := extended_slots hs x
    have hn := Sequence.wf S hΓx hsx e next hp.2.2.2
    have hqwf := Sequence.wf S (extended_pure hΓ a) (extended_slots hs a) e q hq
    have hq'wf := Sequence.wf S (extended_pure hΓx a)
      (extended_slots (Γ := (Ty.base x, (⊥ : ε)) :: Γ) (ts := extendSorts x ambient) hsx a) e q' hq'
    have hrename : q'.source = q.source.wk1 := liftAmbient_source S q x
    have hstep : Eqv Γ (.base c) e
        (.let₁ (.let₁ p.source next.source) q.source)
        (.let₁ p.source (.let₁ next.source q.source.wk1)) :=
      .step (.rewrite (.let₁ (.let₁ hf hn) hqwf)
        (.let₁ hf (.let₁ hn (hrename ▸ hq'wf))) (.let1_let1 _ _ _))
    have htail := ih hp.2.2.2 rfl hΓx hsx q' hq'
    exact hstep.trans (.let1 (.refl hf) (hrename ▸ htail))

public theorem bind_eqv {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ts i))
    (e : ε) (p : Sequence S a ts) (q : Sequence S c (extendSorts a ts))
    (hp : Sequence.WellTyped S e p) (hq : Sequence.WellTyped S e q) :
    letI := S.endpoints
    Eqv Γ (.base c) e (.let₁ p.source q.source) (bind S p q).source :=
  bind_eqv_aux S e p hp rfl hΓ hslots q hq

end Soundness

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.BindProofs

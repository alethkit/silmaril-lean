module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Bind.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Bind.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

/-! # Source equations for substitution and prefix binding in mixed trees -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
  (SumSignature treeSource endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.BindProofs

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {a c : α}
  {n m : Nat} {slots : Fin n → α} {target : Fin m → α}

private theorem tuple_subst {k : Nat} (xs : Fin k → Expr (Φ ⊕ Ψ)) (ξ : Nat → Expr (Φ ⊕ Ψ)) :
    (sourceTuple k xs).subst ξ = sourceTuple k (fun i => (xs i).subst ξ) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [sourceTuple, Expr.subst, ih]

private theorem tree_subst_source (p : Tree S slots c) (σ : Sequence.TreeSubst S slots target)
    (ξ : Nat → Expr (Φ ⊕ Ψ)) (h : ∀ i : Fin n, ξ i.val = treeSource S (σ i)) :
    treeSource S (p.interpret S (Tree S target) Tree.op σ) = (treeSource S p).subst ξ := by
  induction p with
  | var i => exact (h i).symm
  | op f args ih => simp only [Tree.interpret, treeSource, Expr.subst, tuple_subst, ih]

private theorem lift_source (σ : Sequence.TreeSubst S slots target)
    (ξ : Nat → Expr (Φ ⊕ Ψ)) (h : ∀ i : Fin n, ξ i.val = treeSource S (σ i)) (x : α)
    (i : Fin (n + 1)) : Expr.liftSubst ξ i.val = treeSource S (Sequence.liftSubst S σ x i) := by
  refine Fin.cases rfl (fun j => ?_) i
  change (ξ j.val).wk0 =
    treeSource S ((σ j).interpret S (Tree S (extendSorts x target)) Tree.op (fun t => .var t.succ))
  rw [h j, Expr.wk0, Expr.wk_eq_subst]
  exact (tree_subst_source S (σ j) _ _ fun _ => rfl).symm

public theorem subst_source (p : Program S T c slots) (σ : Sequence.TreeSubst S slots target)
    (ξ : Nat → Expr (Φ ⊕ Ψ)) (h : ∀ i : Fin n, ξ i.val = treeSource S (σ i)) :
    (subst S T p σ).source = p.source.subst ξ := by
  induction p generalizing m ξ with
  | ret p => exact tree_subst_source S p σ ξ h
  | @atom k as f args next ih =>
    simp only [subst, Program.source, Expr.subst, tuple_subst, tree_subst_source S _ σ ξ h,
      ih _ _ (lift_source S σ ξ h (S.out f))]
  | @sum k as g args left right ihl ihr =>
    simp only [subst, Program.source, Expr.subst, tuple_subst, tree_subst_source S _ σ ξ h,
      ihl _ _ (lift_source S σ ξ h (T.left g)), ihr _ _ (lift_source S σ ξ h (T.right g))]

private theorem subst0_source (q : Program S T c (extendSorts a slots)) (v : Tree S slots a) :
    (subst S T q (Sequence.subst0 S v)).source = q.source.subst (treeSource S v).subst0 :=
  subst_source S T q _ _ fun i => Fin.cases rfl (fun _ => rfl) i

public theorem weakenUnder_source (q : Program S T c (extendSorts a slots)) (x : α) :
    (weakenUnder S T x q).source = q.source.wk1 := by
  rw [Expr.wk1, Expr.wk_eq_subst]
  exact subst_source S T q _ _ fun i => Fin.cases rfl (fun _ => rfl) i

section Typed

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [Preorder ε] [Bot ε]

omit [HasEff Ψ ε] [Preorder ε] in
private theorem lift_pure (σ : Sequence.TreeSubst S slots target)
    (hσ : ∀ i, DeclaredPure (ε := ε) S (σ i)) (x : α) (i : Fin (n + 1)) :
    DeclaredPure (ε := ε) S (Sequence.liftSubst S σ x i) := by
  refine Fin.cases (motive := fun j =>
    DeclaredPure (ε := ε) S (Sequence.liftSubst S σ x j)) trivial (fun j => ?_) i
  exact Sequence.tree_pure_subst S (σ j) (hσ j) _ fun _ => trivial

public theorem subst_typed (e : ε) (p : Program S T c slots) (hp : Program.WellTyped S T e p)
    (σ : Sequence.TreeSubst S slots target) (hσ : ∀ i, DeclaredPure (ε := ε) S (σ i)) :
    Program.WellTyped S T e (subst S T p σ) := by
  induction p generalizing m with
  | ret p => exact Sequence.tree_pure_subst S p hp σ hσ
  | atom f args next ih =>
    exact ⟨fun i => Sequence.tree_pure_subst S (args i) (hp.1 i) σ hσ, hp.2.1, hp.2.2.1,
      ih hp.2.2.2 _ (lift_pure S σ hσ _)⟩
  | sum g args left right ihl ihr =>
    exact ⟨fun i => Sequence.tree_pure_subst S (args i) (hp.1 i) σ hσ, hp.2.1,
      ihl hp.2.2.1 _ (lift_pure S σ hσ _), ihr hp.2.2.2 _ (lift_pure S σ hσ _)⟩

omit [HasEff Ψ ε] [Preorder ε] in
private theorem liftAmbient_pure (a x : α) (i : Fin (n + 1)) :
    DeclaredPure (ε := ε) S (Sequence.liftAmbientSubst S (slots := slots) a x i) := by
  refine Fin.cases ?_ (fun j => ?_) i <;> exact trivial

public theorem weakenUnder_typed (e : ε) (q : Program S T c (extendSorts a slots))
    (hq : Program.WellTyped S T e q) (x : α) : Program.WellTyped S T e (weakenUnder S T x q) :=
  subst_typed S T e q hq _ (liftAmbient_pure S a x)

public theorem bindPrefix_typed (e : ε) (p : Sequence S a slots)
    (q : Program S T c (extendSorts a slots))
    (hp : Sequence.WellTyped S e p) (hq : Program.WellTyped S T e q) :
    Program.WellTyped S T e (bindPrefix S T p q) := by
  induction p with
  | ret v =>
    exact subst_typed S T e q hq (Sequence.subst0 S v)
      (fun i => Fin.cases (motive := fun j => DeclaredPure (ε := ε) S (Sequence.subst0 S v j))
        hp (fun _ => trivial) i)
  | call f args next ih => exact ⟨hp.1, hp.2.1, hp.2.2.1,
      ih _ hp.2.2.2 (weakenUnder_typed S T e q hq _)⟩

end Typed

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]

private theorem bindPrefix_eqv_aux (e : ε) (p : Sequence S a slots) (hp : Sequence.WellTyped S e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n), Γ.Pure →
      (∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots (i.cast hlen))) →
      ∀ (q : Program S T c (extendSorts a slots)), Program.WellTyped S T e q →
        Eqv Γ (.base c) e (.let₁ (ofSequence S T p).source q.source) (bindPrefix S T p q).source := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  induction p with
  | @ret size ambient v =>
    intro Γ hlen hΓ hs q hq
    subst size
    change Eqv Γ (.base c) e (.let₁ (treeSource S v) q.source)
      (subst S T q (Sequence.subst0 S v)).source
    rw [subst0_source S T]
    exact .step (.let1_beta (Mixed.tree_wf S T hΓ hs v hp ⊥)
      (source_wf S T (pure_extended hΓ a) (slots_extended hs) e q hq))
  | @call size ambient f args next ih =>
    intro Γ hlen hΓ hs q hq
    subst size
    let x := S.out f
    let request : Expr (Φ ⊕ Ψ) := .op (.inl f)
      (sourceTuple (S.arity f) (fun i => treeSource S (args i)))
    let q' := weakenUnder S T x q
    have hq' := weakenUnder_typed S T e q hq x
    have hf := atom_request_wf S T hΓ hs args hp.1 hp.2.2.1
    have hΓx := pure_extended hΓ x
    have hsx := slots_extended (a := x) hs
    have hn := source_wf S T hΓx hsx e (ofSequence S T next)
      ((ofSequence_wellTyped S T e next).mpr hp.2.2.2)
    have hqwf := source_wf S T (pure_extended hΓ a) (slots_extended hs) e q hq
    have hq'wf := source_wf S T (pure_extended hΓx a) (slots_extended hsx) e q' hq'
    have hrename := weakenUnder_source S T q x
    have hstep : Eqv Γ (.base c) e
        (.let₁ (.let₁ request (ofSequence S T next).source) q.source)
        (.let₁ request (.let₁ (ofSequence S T next).source q.source.wk1)) :=
      .step (.rewrite (.let₁ (.let₁ hf hn) hqwf)
        (.let₁ hf (.let₁ hn (hrename ▸ hq'wf))) (.let1_let1 _ _ _))
    have htail := ih hp.2.2.2 rfl hΓx hsx q' hq'
    exact hstep.trans (.let1 (.refl hf) (hrename ▸ htail))

public theorem bindPrefix_eqv {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α}
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ss i)) (e : ε)
    (p : Sequence S a ss) (q : Program S T c (extendSorts a ss))
    (hp : Sequence.WellTyped S e p) (hq : Program.WellTyped S T e q) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ (.base c) e (.let₁ (ofSequence S T p).source q.source) (bindPrefix S T p q).source :=
  bindPrefix_eqv_aux S T e p hp rfl hΓ hslots q hq

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.BindProofs

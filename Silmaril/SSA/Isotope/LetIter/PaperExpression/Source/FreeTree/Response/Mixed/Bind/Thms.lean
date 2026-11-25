module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Bind.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Bind.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Bind

/-! # Pure substitution and fixed-bound prefix normalization -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
  (SumSignature treeSource endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {a c : α}
  {n m : Nat} {slots : Fin n → α} {target : Fin m → α}

theorem tree_subst_source (p : Tree S slots c) (σ : Sequence.TreeSubst S slots target)
    (ξ : Nat → Expr (Φ ⊕ Ψ)) (h : ∀ i : Fin n, ξ i.val = treeSource S (σ i)) :
    treeSource S (p.interpret S (Tree S target) Tree.op σ) = (treeSource S p).subst ξ :=
  BindProofs.tree_subst_source S p σ ξ h

theorem subst_source (p : Program S T c slots) (σ : Sequence.TreeSubst S slots target)
    (ξ : Nat → Expr (Φ ⊕ Ψ)) (h : ∀ i : Fin n, ξ i.val = treeSource S (σ i)) :
    (subst S T p σ).source = p.source.subst ξ :=
  BindProofs.subst_source S T p σ ξ h

theorem weakenUnder_source (q : Program S T c (extendSorts a slots)) (x : α) :
    (weakenUnder S T x q).source = q.source.wk1 :=
  BindProofs.weakenUnder_source S T q x

section Typed

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [Preorder ε] [Bot ε]

theorem subst_typed (e : ε) (p : Program S T c slots) (hp : Program.WellTyped S T e p)
    (σ : Sequence.TreeSubst S slots target) (hσ : ∀ i, DeclaredPure (ε := ε) S (σ i)) :
    Program.WellTyped S T e (subst S T p σ) :=
  BindProofs.subst_typed S T e p hp σ hσ

theorem weakenUnder_typed (e : ε) (q : Program S T c (extendSorts a slots))
    (hq : Program.WellTyped S T e q) (x : α) : Program.WellTyped S T e (weakenUnder S T x q) :=
  BindProofs.weakenUnder_typed S T e q hq x

theorem bindPrefix_typed (e : ε) (p : Sequence S a slots)
    (q : Program S T c (extendSorts a slots))
    (hp : Sequence.WellTyped S e p) (hq : Program.WellTyped S T e q) :
    Program.WellTyped S T e (bindPrefix S T p q) :=
  BindProofs.bindPrefix_typed S T e p q hp hq

end Typed

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]

/-- The prefix let normalizes at the supplied source bound. -/
theorem bindPrefix_eqv {Γ : EffectCtx (Ty α) ε} {ss : Fin Γ.length → α}
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ss i)) (e : ε)
    (p : Sequence S a ss) (q : Program S T c (extendSorts a ss))
    (hp : Sequence.WellTyped S e p) (hq : Program.WellTyped S T e q) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ (.base c) e (.let₁ (ofSequence S T p).source q.source) (bindPrefix S T p q).source :=
  BindProofs.bindPrefix_eqv S T hΓ hslots e p q hp hq

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

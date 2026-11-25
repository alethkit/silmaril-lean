module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Bind.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Bind

/-! # Binding normalized call sequences at an original source bound -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence

universe u r

variable {α Φ : Type u} (S : Signature α Φ) {a c : α}
  {n m : Nat} {slots : Fin n → α} {target : Fin m → α}

/-- Typed tree substitution computes the corresponding source substitution. -/
theorem subst_source (p : Sequence S c slots) (σ : TreeSubst S slots target)
    (ξ : Nat → Expr Φ) (h : ∀ i : Fin n, ξ i.val = (σ i).source) :
    (subst S p σ).source = p.source.subst ξ :=
  BindProofs.subst_source S p σ ξ h

theorem weaken_source (p : Sequence S c slots) (x : α) :
    (weaken S x p).source = p.source.wk0 :=
  BindProofs.weaken_source S p x

section Typed

variable {ε : Type r} [HasEff Φ ε] [Preorder ε] [Bot ε]

theorem subst_typed (e : ε) (p : Sequence S c slots) (hp : Sequence.WellTyped S e p)
    (σ : TreeSubst S slots target) (hσ : ∀ i, DeclaredPure (ε := ε) S (σ i)) :
    Sequence.WellTyped S e (subst S p σ) :=
  BindProofs.subst_typed S e p hp σ hσ

theorem weaken_typed (x : α) (e : ε) (p : Sequence S c slots) (hp : Sequence.WellTyped S e p) :
    Sequence.WellTyped S e (weaken S x p) :=
  BindProofs.weaken_typed S x e p hp

theorem bind_typed (e : ε) (p : Sequence S a slots) (q : Sequence S c (extendSorts a slots))
    (hp : Sequence.WellTyped S e p) (hq : Sequence.WellTyped S e q) :
    Sequence.WellTyped S e (bind S p q) :=
  BindProofs.bind_typed S e p q hp hq

end Typed

variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]

/-- Flatten a let between two sequences by reassociation and pure beta. -/
theorem bind_eqv {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ts i))
    (e : ε) (p : Sequence S a ts) (q : Sequence S c (extendSorts a ts))
    (hp : Sequence.WellTyped S e p) (hq : Sequence.WellTyped S e q) :
    letI := S.endpoints
    Eqv Γ (.base c) e (.let₁ p.source q.source) (bind S p q).source :=
  BindProofs.bind_eqv S hΓ hslots e p q hp hq

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence

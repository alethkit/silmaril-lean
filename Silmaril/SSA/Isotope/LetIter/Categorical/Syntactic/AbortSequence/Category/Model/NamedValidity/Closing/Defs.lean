module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.NamedValidity.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.NamedValidity.ClosingTyping

/-! # Closing typed LetIter judgments -/

@[expose] public section

open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation HasType)

universe u v w

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.NamedContext

variable {ν : Type w} {τ : Type u} {Φ : Type v}

set_option backward.isDefEq.respectTransparency false

theorem lookupSlot_eq_lookup [DecidableEq ν] (x : ν) (Γ : Ctx ν τ) :
    (lookupSlot x Γ).map (freeSlots Γ).get = Γ.lookup x :=
  Proofs.lookupSlot_eq_lookup x Γ

theorem prepend_get_free {k n : Nat} (α : BoundCtx τ k) (β : BoundCtx τ n) (i : Fin k) :
    (prepend α β).get (freeIndex i n) = α.get i :=
  Proofs.prepend_get_free α β i

theorem prepend_get_bound {k n : Nat} (α : BoundCtx τ k) (β : BoundCtx τ n) (i : Fin n) :
    (prepend α β).get (boundIndex k i) = β.get i :=
  Proofs.prepend_get_bound α β i

section Typing

variable [DecidableEq ν] [TypeFormers τ] [HasTy Φ τ] {Γ : Ctx ν τ}

/-- Move named slots behind the bound context without changing the result type. -/
def closeDerivation :
    {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν Φ n} → {A : τ} →
      Derivation Φ Γ β t A →
      Derivation Φ (Ctx.nil : Ctx Empty τ) (prepend (freeSlots Γ) β) (closeTm Γ t) A
  | n, β, _, A, .fv (x := x) h => by
    have slot := (lookupSlot_eq_lookup x Γ).trans h
    cases hs : lookupSlot x Γ with
    | none => simp [hs] at slot
    | some i =>
      have hi : (freeSlots Γ).get i = A := Option.some.inj (by simpa [hs] using slot)
      rw [closeTm, hs]
      exact ((prepend_get_free (freeSlots Γ) β i).trans hi) ▸ .bv
  | _, β, _, _, .bv (ι := i) => (prepend_get_bound (freeSlots Γ) β i) ▸ .bv
  | _, _, _, _, .op d => .op (closeDerivation d)
  | _, _, _, _, .let₁ d e => .let₁ (closeDerivation d) (closeDerivation e)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair d e => .pair (closeDerivation d) (closeDerivation e)
  | _, _, _, _, .let₂ d e => .let₂ (closeDerivation d) (closeDerivation e)
  | _, _, _, _, .inl d => .inl (closeDerivation d)
  | _, _, _, _, .inr d => .inr (closeDerivation d)
  | _, _, _, _, .case d e f => .case (closeDerivation d) (closeDerivation e) (closeDerivation f)
  | _, _, _, _, .abort d => .abort (closeDerivation d)
  | _, _, _, _, .iter d e => .iter (closeDerivation d) (closeDerivation e)

theorem closeHasType {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) :
    HasType Φ (Ctx.nil : Ctx Empty τ) (prepend (freeSlots Γ) β) (closeTm Γ t) A := by
  obtain ⟨d⟩ := Derivation.ofHasType h
  exact (closeDerivation d).toHasType

end Typing

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.NamedContext

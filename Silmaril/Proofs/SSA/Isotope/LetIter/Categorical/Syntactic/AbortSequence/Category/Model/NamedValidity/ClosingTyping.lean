module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.NamedValidity.Defs

open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation HasType AbortEquiv)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w r u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.NamedContext.Proofs

open NamedContext

variable {ν : Type w} {τ : Type u} {Φ : Type v}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

public theorem lookupSlot_eq_lookup [DecidableEq ν] (x : ν) (Γ : Ctx ν τ) :
    (lookupSlot x Γ).map (freeSlots Γ).get = Γ.lookup x := by
  induction Γ with
  | nil => rfl
  | snoc Γ name A ih =>
    have step (xslots : Option (Fin Γ.length)) :
        (xslots.map Fin.succ).map (freeSlots (.snoc Γ name A)).get =
          xslots.map (freeSlots Γ).get := by cases xslots <;> rfl
    cases name with
    | none => exact (step (lookupSlot x Γ)).trans ih
    | some y =>
      by_cases h : x = y
      · simp only [lookupSlot, Ctx.lookup, ite_eq_left h]
        rfl
      · simp only [lookupSlot, Ctx.lookup, ite_eq_right h]
        exact (step (lookupSlot x Γ)).trans ih

public theorem prepend_get_free {k n : Nat} (α : BoundCtx τ k) (β : BoundCtx τ n) (i : Fin k) :
    (prepend α β).get (freeIndex i n) = α.get i := by
  induction β with
  | nil => rfl
  | snoc β A ih => exact ih

public theorem prepend_get_bound {k n : Nat} (α : BoundCtx τ k) (β : BoundCtx τ n) (i : Fin n) :
    (prepend α β).get (boundIndex k i) = β.get i := by
  induction β with
  | nil => exact i.elim0
  | snoc β A ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact ih j

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.NamedContext.Proofs

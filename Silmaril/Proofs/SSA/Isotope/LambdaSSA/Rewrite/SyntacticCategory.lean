module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Defs

/-! # Syntactic category arrows are single-exit region classes -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open SyntacticCategory (ofType ofRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

theorem ofRegion_eq_iff {A B : τ} {r s : Region Φ}
    (hr : ValueBranches (A :: Γ) r [B]) (hs : ValueBranches (A :: Γ) s [B]) :
    ofRegion hr = ofRegion hs ↔ SubstitutionEquiv (A :: Γ) r s [B] := by
  constructor
  · intro h
    exact ContinuationFamily.toHom_eq_iff.mp
      (congrArg (fun f => f.hom) h) (show At [A] 0 A from rfl)
  · intro h
    apply InducedCategory.hom_ext
    apply ContinuationFamily.toHom_eq_iff.mpr
    intro i D hi
    have eq : D = A := List.mem_singleton.mp (List.mem_of_getElem? hi)
    cases eq
    exact h

theorem exists_region {A B : τ}
    (f : ofType (Φ := Φ) A ⟶ ofType (Γ := Γ) B) :
    ∃ (r : Region Φ) (hr : ValueBranches (A :: Γ) r [B]), ofRegion hr = f := by
  obtain ⟨σ, hσ⟩ := Quotient.exists_rep f.hom
  have hr := σ.property (show At [A] 0 A from rfl)
  refine ⟨σ.val 0, hr, InducedCategory.hom_ext ?_⟩
  rw [← hσ]
  apply ContinuationFamily.toHom_eq_iff.mpr
  intro i D hi
  cases i with
  | zero =>
    have eq : D = A := List.mem_singleton.mp (List.mem_of_getElem? hi)
    cases eq
    exact .base (.refl hr.hasType)
  | succ i => simp [At, ContinuationContext.single] at hi

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

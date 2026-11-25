module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Defs

/-! # Representatives of singleton arrows in the paper relation -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Singleton

open CategoryTheory Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Region.Paper (Eqv toHom_eq_iff)
open Region.Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ}

theorem ofRegion_eq_iff {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B]) :
    ofRegion hr = ofRegion hs ↔ Eqv [A] r s [B] := by
  constructor
  · intro e
    exact toHom_eq_iff.mp (congrArg InducedCategory.Hom.hom e) (i := 0) rfl
  · intro h
    apply InducedCategory.hom_ext
    apply toHom_eq_iff.mpr
    intro i D hi
    cases List.mem_singleton.mp (List.mem_of_getElem? hi)
    exact h

theorem exists_ofRegion (f : ofType (Φ := Φ) A ⟶ ofType B) :
    ∃ (r : Region Φ) (hr : ValueBranches [A] r [B]), f = ofRegion hr := by
  obtain ⟨f⟩ := f
  change Paper.Hom [] [A] [B] at f
  induction f using Quotient.inductionOn with
  | h family =>
    refine ⟨family.val 0, family.property (ℓ := 0) rfl, InducedCategory.hom_ext ?_⟩
    apply toHom_eq_iff.mpr
    intro i D hi
    have idx : i = 0 := by
      cases i with
      | zero => rfl
      | succ i => simp [At] at hi
    subst i
    exact .cfgEta (.native (.base (.refl (family.property hi).hasType)))

theorem ofRegion_id (A : τ) :
    ofRegion (Φ := Φ) (r := .br 0 (.var 0)) (.br rfl (.var rfl)) =
      𝟙 (ofType A) := by
  apply InducedCategory.hom_ext
  apply toHom_eq_iff.mpr
  intro i D hi
  have idx : i = 0 := by
    cases i with
      | zero => rfl
      | succ i => simp [At] at hi
  subst i
  exact .cfgEta (.native (.base (.refl (Region.HasType.br hi (.var rfl)))))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Singleton

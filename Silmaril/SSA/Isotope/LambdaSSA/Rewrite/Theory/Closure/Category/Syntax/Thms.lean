module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Thms
public import Mathlib.CategoryTheory.Adjunction.Limits
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SyntacticCategory

/-! # The native type category and its region representatives -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- The singleton type presentation includes all continuation interfaces up to
isomorphism, by native exit packing. -/
instance toContinuation_isEquivalence : (toContinuation Φ Γ).IsEquivalence where
  essSurj := ⟨fun X => ⟨ofType (packedExitType X.labels), X.nonempty_packedIso.map Iso.symm⟩⟩

/-- Passing to singleton types is an equivalence of syntactic categories. -/
noncomputable def continuationEquivalence :
    SyntacticCategory Φ Γ ≌ ContinuationContext Φ Γ :=
  (toContinuation Φ Γ).asEquivalence

instance hasFiniteCoproducts : HasFiniteCoproducts (SyntacticCategory Φ Γ) :=
  ⟨fun _ => Adjunction.hasColimitsOfShape_of_equivalence (toContinuation Φ Γ)⟩

/-- Equality of arrows represented by typed regions is exactly their native
rewrite equivalence. -/
theorem ofRegion_eq_iff {A B : τ} {r s : Region Φ}
    (hr : ValueBranches (A :: Γ) r [B]) (hs : ValueBranches (A :: Γ) s [B]) :
    ofRegion hr = ofRegion hs ↔ SubstitutionEquiv (A :: Γ) r s [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.ofRegion_eq_iff hr hs

/-- Equality after binding characterizes native equivalence of the two
normalized regions. -/
theorem ofTypedRegion_eq_iff {A B : τ} {r s : Region Φ}
    (hr : HasType (A :: Γ) r [B]) (hs : HasType (A :: Γ) s [B]) :
    ofTypedRegion hr = ofTypedRegion hs ↔
      SubstitutionEquiv (A :: Γ) r.bindBranchArguments s.bindBranchArguments [B] :=
  ofRegion_eq_iff hr.bindBranchArguments hs.bindBranchArguments

/-- Native rewrites give the same syntactic arrow after binding. -/
theorem ofTypedRegion_congr {A B : τ} {r s : Region Φ}
    (h : SubstitutionEquiv (A :: Γ) r s [B]) (hr : HasType (A :: Γ) r [B]) (hs : HasType (A :: Γ) s [B]) :
    ofTypedRegion hr = ofTypedRegion hs :=
  (ofTypedRegion_eq_iff hr hs).mpr h.bindBranchArguments

/-- Every native arrow between types has a one-input, one-exit region
representative. -/
theorem exists_region {A B : τ}
    (f : ofType (Φ := Φ) A ⟶ ofType (Γ := Γ) B) :
    ∃ (r : Region Φ) (hr : ValueBranches (A :: Γ) r [B]), ofRegion hr = f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.exists_region f

end Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory

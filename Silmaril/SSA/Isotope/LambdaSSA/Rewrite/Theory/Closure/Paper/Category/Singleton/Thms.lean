module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Singleton

/-! # Empty-capture singleton representatives -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B C : τ}

theorem ofRegion_eq_iff {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B]) :
    ofRegion hr = ofRegion hs ↔ Eqv [A] r s [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Singleton.ofRegion_eq_iff hr hs

theorem exists_ofRegion (f : ofType (Φ := Φ) A ⟶ ofType B) :
    ∃ (r : Region Φ) (hr : ValueBranches [A] r [B]), f = ofRegion hr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Singleton.exists_ofRegion f

theorem ofRegion_id (A : τ) :
    ofRegion (Φ := Φ) (r := .br 0 (.var 0)) (.br rfl (.var rfl)) =
      𝟙 (ofType A) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Singleton.ofRegion_id A

theorem ofRegion_comp {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [B] s [C])
    (hrs : ValueBranches [A] (compLSubst (fun _ => r) (fun _ => s) 0) [C]) :
    ofRegion hr ≫ ofRegion hs = ofRegion hrs := rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

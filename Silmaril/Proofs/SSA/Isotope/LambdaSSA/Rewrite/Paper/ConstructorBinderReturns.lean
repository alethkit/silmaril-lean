module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Thms

/-! # Central pure returns of constructor products and cases -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorBinderReturns

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Region.Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {X A B D : τ} {a b c l r : Tm Φ}

theorem let₂_pair {a b c : Tm Φ} (ha : Tm.BranchValue [X] a A)
    (hb : Tm.BranchValue [X] b B) (hc : Tm.BranchValue [B, A, X] c D) :
    CentralPureReturn pe (ofRegion (.let₂ (.pair ha.hasType hb.hasType) (.br (ℓ := 0) rfl hc))) := by
  have h : Tm.BranchValue [X] (c.subst (Tm.consSubst b (Tm.singleSubst a))) D := by
    apply hc.subst
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact hb
    | succ i =>
      cases i with
      | zero => cases Option.some.inj hi; exact ha
      | succ _ => exact .var hi
  have eq : Paper.Eqv [X] (.let₂ (.pair a b) (.br 0 c))
      (.br 0 (c.subst (Tm.consSubst b (Tm.singleSubst a)))) [D] :=
    .productBeta (.let₂Beta ha hb (.br (ℓ := 0) rfl hc.hasType))
  exact ((ofRegion_eq_iff _ (.br (ℓ := 0) rfl h)).mpr eq).symm ▸ centralPureReturn_branchValue pe h

theorem case_inl (ha : Tm.BranchValue [X] a A)
    (hl : Tm.BranchValue [A, X] l D) (hr : Tm.BranchValue [B, X] r D) :
    CentralPureReturn pe (ofRegion (.case (.inl ha.hasType) (.br (ℓ := 0) rfl hl) (.br (ℓ := 0) rfl hr))) := by
  have h := ha.singleSubst hl
  have eq : Paper.Eqv [X] (.case (.inl a) (.br 0 l) (.br 0 r))
      (.br 0 (l.subst (Tm.singleSubst a))) [D] :=
    (.cfgEta (.native (.base (.caseInl ha.hasType (.br (ℓ := 0) rfl hl.hasType) (.br (ℓ := 0) rfl hr.hasType)))) :
      Paper.Eqv [X] _ (.let₁ a (.br 0 l)) [D]).trans
      (.cfgEta (.native (.base (.letBr ha hl rfl))))
  exact ((ofRegion_eq_iff _ (.br (ℓ := 0) rfl h)).mpr eq).symm ▸ centralPureReturn_branchValue pe h

theorem case_inr (hb : Tm.BranchValue [X] b B)
    (hl : Tm.BranchValue [A, X] l D) (hr : Tm.BranchValue [B, X] r D) :
    CentralPureReturn pe (ofRegion (.case (.inr hb.hasType) (.br (ℓ := 0) rfl hl) (.br (ℓ := 0) rfl hr))) := by
  have h := hb.singleSubst hr
  have eq : Paper.Eqv [X] (.case (.inr b) (.br 0 l) (.br 0 r))
      (.br 0 (r.subst (Tm.singleSubst b))) [D] :=
    (.cfgEta (.native (.base (.caseInr hb.hasType (.br (ℓ := 0) rfl hl.hasType) (.br (ℓ := 0) rfl hr.hasType)))) :
      Paper.Eqv [X] _ (.let₁ b (.br 0 r)) [D]).trans
      (.cfgEta (.native (.base (.letBr hb hr rfl))))
  exact ((ofRegion_eq_iff _ (.br (ℓ := 0) rfl h)).mpr eq).symm ▸ centralPureReturn_branchValue pe h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorBinderReturns

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorBinderReturns

/-! # Central pure returns of constructor products and selected cases -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {X A B D : τ} {a b c l r : Tm Φ}

/-- A returned constructor value after destructuring a constructor pair is central and pure. -/
theorem centralPureReturn_let₂_pair (ha : Tm.BranchValue [X] a A)
    (hb : Tm.BranchValue [X] b B) (hc : Tm.BranchValue [B, A, X] c D) :
    CentralPureReturn pe (ofRegion (.let₂ (.pair ha.hasType hb.hasType) (.br (ℓ := 0) rfl hc))) :=
  ConstructorBinderReturns.let₂_pair pe ha hb hc

/-- A returned constructor value after selecting the left constructor tag is central and pure. -/
theorem centralPureReturn_case_inl (ha : Tm.BranchValue [X] a A)
    (hl : Tm.BranchValue [A, X] l D) (hr : Tm.BranchValue [B, X] r D) :
    CentralPureReturn pe (ofRegion (.case (.inl ha.hasType) (.br (ℓ := 0) rfl hl) (.br (ℓ := 0) rfl hr))) :=
  ConstructorBinderReturns.case_inl pe ha hl hr

/-- A returned constructor value after selecting the right constructor tag is central and pure. -/
theorem centralPureReturn_case_inr (hb : Tm.BranchValue [X] b B)
    (hl : Tm.BranchValue [A, X] l D) (hr : Tm.BranchValue [B, X] r D) :
    CentralPureReturn pe (ofRegion (.case (.inr hb.hasType) (.br (ℓ := 0) rfl hl) (.br (ℓ := 0) rfl hr))) :=
  ConstructorBinderReturns.case_inr pe hb hl hr

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Chosen.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.BinaryProducts.Thms

/-! # Exact guarded distributivity maps for the case-return quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase (distributorIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
  (discardPreservingUnitIsTerminal discardPreservingFan discardPreservingBinaryFanIsLimit)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Obj" => Paper.Extension.Singleton.ofType (Φ := Φ) Seed
set_option hygiene false in
local notation "P" => Paper.WithCaseReturns.projection (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Values" => Paper.WithCaseReturns.ValueCategory (τ := τ) (Φ := Φ) pe
local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod

/-- The exact guarded map from a retained sum to the sum of retained factors. -/
noncomputable abbrev guardedDistributorIso (X A B : τ) :
    Obj (X ×ₜ (A ⊕ₜ B)) ≅ Obj ((X ×ₜ A) ⊕ₜ (X ×ₜ B)) :=
  (P).mapIso (distributorIso X A B)

/-- The Cartesian tensor chooses the exact syntax products and unit. -/
noncomputable abbrev valueCartesian : CartesianMonoidalCategory Values :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    ⟨_, discardPreservingUnitIsTerminal Seed pe (Paper.WithCaseReturns.includeUnit pe)⟩
    (fun A B => ⟨discardPreservingFan Seed pe (Paper.WithCaseReturns.includeProjection pe) A.obj.as B.obj.as,
      discardPreservingBinaryFanIsLimit Seed pe A.obj.as B.obj.as (Paper.WithCaseReturns.includeProjection pe)⟩)

/-- The direct expression candidate for the guarded inverse distributor. -/
def distributorTerm : Tm Φ :=
  .let₂ (.var 0) (.case (.var 0)
    (.inl (.pair (.var 2) (.var 0))) (.inr (.pair (.var 2) (.var 0))))

theorem distributorTerm_typed (X A B : τ) :
    Tm.HasType [X ×ₜ (A ⊕ₜ B)] (distributorTerm : Tm Φ) ((X ×ₜ A) ⊕ₜ (X ×ₜ B)) :=
  .let₂ (.var (i := 0) rfl) (.case (.var (i := 0) rfl)
    (.inl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))
    (.inr (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))))

theorem distributorTerm_pure : Tm.Pure pe (distributorTerm : Tm Φ) :=
  .let₂ .var (.case .var (.inl (.pair .var .var)) (.inr (.pair .var .var)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns

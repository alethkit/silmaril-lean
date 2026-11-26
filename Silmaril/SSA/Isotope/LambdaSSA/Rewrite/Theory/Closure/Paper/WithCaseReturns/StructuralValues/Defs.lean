module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Distributor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Thms

/-! # Structural values in the opt-in case-return quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (ofType)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

abbrev ValueCategory :=
  Extension.Singleton.StructuralValues.ValueCategory (JoinedStep (τ := τ) (Φ := Φ) pe)

abbrev inclusion : ValueCategory (τ := τ) (Φ := Φ) pe ⥤ TypeCategory (τ := τ) (Φ := Φ) pe :=
  Extension.Singleton.StructuralValues.inclusion (JoinedStep pe)

abbrev ofSyntaxType (A : τ) : ValueCategory (τ := τ) (Φ := Φ) pe :=
  ⟨ofType (JoinedStep pe) A⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

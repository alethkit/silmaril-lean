module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.ConstructorValues.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithUnitEtaConstructorValues

/-! # Terminality for projected constructor returns -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

instance constructorValues_faithful : (constructorValues (τ := τ) (Φ := Φ)).Faithful :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithUnitEtaConstructorValues.constructorValues_faithful

/-- The syntax unit is terminal among constructor returns with equality
inherited from the opt-in unit extension. -/
noncomputable def constructorUnitIsTerminal :
    IsTerminal (constructorUnit (τ := τ) (Φ := Φ)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithUnitEtaConstructorValues.constructorUnitIsTerminal

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithUnitEta

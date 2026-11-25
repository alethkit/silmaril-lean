module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs

/-! # A state update with unary β under both pair and sum
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors.Example

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.UnaryReturn Paper.RetainedLet
open scoped Paper.BoundSimulation.Obstruction

def source : Ty Empty := .coprod .unit .unit
def target : Ty Empty := .coprod (.product source source) .unit
def update : Tm Empty := .inl (.pair (.let₁ (.var 0) (.var 0)) (.var 0))
def constructor : Tm Empty := .inl (.pair (.var 0) (.var 0))

theorem update_normalizes : Normalizes [source] update constructor target :=
  .inl (.pair (.ofBeta (.let₁ (.value (.var (i := 0) rfl)) (.value (.var (i := 0) rfl))))
    (.value (.var (i := 0) rfl)))

/-- The left product state retains the old state in its second component.
A left old state recurs, and a right one returns unit. -/
def stepBody : Region Empty :=
  .case (.var 0)
    (.let₂ (.var 0) (.case (.var 0)
      (.br 0 (.inr (.inl (.var 0)))) (.br 0 (.inl .unit))))
    (.br 0 (.inl .unit))

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors.Example

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Defs

/-! # The same free profile after adding case returns -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ITree.Reflection

open CategoryTheory

abbrev caseProjection := Paper.WithCaseReturns.projection (τ := Ty Atom) (Φ := Op) false

abbrev projectionUnit := Paper.WithProjectionReturnsAndUnitEta.projection (τ := Ty Atom) (Φ := Op)

/-- Both alternatives destructure a pair and return its first component. The
first producer contains a unary identity let inside the pair. -/
def nestedPair : Region Op :=
  .case (.var 0)
    (.let₁ (.let₂ (.pair (.let₁ (.var 0) (.var 0)) (.var 0)) (.var 1)) (.br 0 (.var 0)))
    pollRegion

def plainPair : Region Op :=
  .case (.var 0)
    (.let₁ (.let₂ (.pair (.var 0) (.var 0)) (.var 1)) (.br 0 (.var 0)))
    pollRegion

theorem nestedPair_typed : ValueBranches [Input] nestedPair [Output] :=
  .case (.var rfl)
    (.let₁ (.let₂ (.pair (.let₁ (.var rfl) (.var rfl)) (.var rfl)) (.var rfl)) (.br rfl (.var rfl)))
    (.let₁ (.op (.var rfl)) (.br rfl (.var rfl)))

theorem plainPair_typed : ValueBranches [Input] plainPair [Output] :=
  .case (.var rfl)
    (.let₁ (.let₂ (.pair (.var rfl) (.var rfl)) (.var rfl)) (.br rfl (.var rfl)))
    (.let₁ (.op (.var rfl)) (.br rfl (.var rfl)))

def nestedPairArrow : ofType (Φ := Op) Input ⟶ ofType Output := ofRegion nestedPair_typed

def plainPairArrow : ofType (Φ := Op) Input ⟶ ofType Output := ofRegion plainPair_typed

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ITree.Reflection

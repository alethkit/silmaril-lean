module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Example.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Constructors

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.UnaryReturn Paper.RetainedLet
open Paper.TypeCategory Paper.BoundSimulation
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Region.Paper.UnaryReturn.Beta.Constructors.Example
open scoped Paper.BoundSimulation.Obstruction

theorem stepBody_typed :
    ValueBranches [target] stepBody [Silmaril.coprod (.unit : Ty Empty) source] :=
  .case (.var (i := 0) rfl)
    (.let₂ (.var (i := 0) rfl)
      (.case (.var (i := 0) rfl)
        (.br (ℓ := 0) rfl (.inr (.inl (.var (i := 0) rfl)))) (.br (ℓ := 0) rfl (.inl .unit))))
    (.br (ℓ := 0) rfl (.inl .unit))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta.Constructors

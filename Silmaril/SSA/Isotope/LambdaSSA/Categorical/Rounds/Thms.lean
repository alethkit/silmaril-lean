module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Rounds.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.RoundsIteration

/-! # Unrolling holds in every Elgot Freyd category -/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [ElgotFreydCategory J]

/-- The loop on any number of rounds of a step whose state is a pure
object is the loop on one round. The step and its exit object are
arbitrary. The proof uses the fixpoint, naturality and codiagonal laws,
and uniformity along three kinds of pure map: the entry of a chain of
phases, the injection of its later phases, and the map forgetting the
phase. It uses preservation of binary coproducts by `J`. -/
theorem iterate_roundsStep {X : V} {Y : C} (h : J.obj X ⟶ Y ⨿ J.obj X) (n : Nat) :
    iterate (roundsStep h n) = iterate h :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.RoundsIteration.iterate_roundsStep J h n

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical

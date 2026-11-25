module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.LocalPairing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MiddleFourInterchange

/-! # Reordering two central computations in the guarded middle-four shuffle -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local infixr:70 " ×ₜ " => product

/-- The literal shuffle reassociates, swaps the two middle factors, and reassociates back. -/
theorem middleFour_factorization (A C B D : τ) :
    middleFour (Φ := Φ) A C B D =
      associate A C (B ×ₜ D) ≫ whiskerLeft (Obj A)
        (unassociate C B D ≫ whiskerRight (braid C B) (Obj D) ≫ associate B C D) ≫
        unassociate A B (C ×ₜ D) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MiddleFourInterchange.middleFour_factorization A C B D

/-- In the swap, the second arrow interchanges with the first by its left centrality square. -/
theorem tensorSequence_braid_of_central {A B X Y : τ}
    (f : Obj X ⟶ Obj A) {g : Obj Y ⟶ Obj B} (hg : WhiskerCentral g) :
    tensorSequence f g ≫ braid A B = braid X Y ≫ tensorSequence g f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MiddleFourInterchange.tensorSequence_braid_of_central f hg

/-- Centrality permits the order change even when the two input types differ. -/
theorem middleFour_tensorSequence {X Y A B : τ}
    {f : Obj X ⟶ Obj A} {g : Obj Y ⟶ Obj B} (hf : WhiskerCentral f) (hg : WhiskerCentral g) :
    middleFour X X Y Y ≫ tensorSequence (tensorSequence f g) (tensorSequence f g) =
      tensorSequence (tensorSequence f f) (tensorSequence g g) ≫ middleFour A A B B :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MiddleFourInterchange.middleFour_tensorSequence hf hg

/-- The canonical pairing preserves centrality and copying. -/
theorem centralCopies_pair {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : CentralCopies f) (hg : CentralCopies g) : CentralCopies (pairArrows f g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MiddleFourInterchange.centralCopies_pair hf hg

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

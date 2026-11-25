module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Structure.Defs
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Associator

/-! # Associator naturality for arbitrary exact λiter computations -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open scoped MonoidalCategory

variable {S : Sig.{u}}

/-- The syntactic computation associator agrees with the value associator. -/
theorem tensorAssociator_value (A B C : ValueCat S) :
    tensorAssociator A.obj B.obj C.obj = (values S).mapIso (α_ A B C) := by rfl

/-- The associator is natural for an arbitrary computation in the first slot. -/
theorem tensorAssociator_naturality_left {A A' : SynCat S} (f : A ⟶ A') (B C : SynCat S) :
    tensorRight C (tensorRight B f) ≫ (tensorAssociator A' B C).hom =
      (tensorAssociator A B C).hom ≫ tensorRight (productObj B C) f :=
  tensorAssociator_naturality_left_proof f B C

/-- The associator is natural for an arbitrary computation in the middle slot. -/
theorem tensorAssociator_naturality_middle (A : SynCat S) {B B' : SynCat S}
    (f : B ⟶ B') (C : SynCat S) :
    tensorRight C (tensorLeft A f) ≫ (tensorAssociator A B' C).hom =
      (tensorAssociator A B C).hom ≫ tensorLeft A (tensorRight C f) :=
  tensorAssociator_naturality_middle_proof A f C

/-- The associator is natural for an arbitrary computation in the last slot. -/
theorem tensorAssociator_naturality_right (A B : SynCat S) {C C' : SynCat S}
    (f : C ⟶ C') :
    tensorLeft (productObj A B) f ≫ (tensorAssociator A B C').hom =
      (tensorAssociator A B C).hom ≫ tensorLeft A (tensorLeft B f) :=
  tensorAssociator_naturality_right_proof A B f

end Silmaril.Thesis.LambdaIter.Syn.SynCat

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Copy.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductCopy

/-! # Diagonal equations for constructor returns and sequential composition -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
local notation "obj" => Paper.TypeCategory.ofType (Φ := Φ)

/-- Sequential pairing of constructor returns is the return of their constructor pair. -/
theorem pairArrows_branchValue {X A B : τ} {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    pairArrows (ofRegion (.br (ℓ := 0) rfl ha)) (ofRegion (.br (ℓ := 0) rfl hb)) =
      ofRegion (.br (ℓ := 0) rfl (.pair ha hb)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductCopy.pairArrows_branchValue ha hb

/-- A constructor return preserves the diagonal. -/
theorem pairArrows_copy_branchValue {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    pairArrows (ofRegion (.br (ℓ := 0) rfl ha)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion (.br (ℓ := 0) rfl ha) ≫ diagonalArrow A :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductCopy.pairArrows_copy_branchValue ha

/-- The lowered return of a constructor value preserves the diagonal. -/
theorem pairArrows_copy_returnTerm_branchValue {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    pairArrows (returnTerm ha.hasType) (returnTerm ha.hasType) = returnTerm ha.hasType ≫ diagonalArrow A :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductCopy.pairArrows_copy_returnTerm_branchValue ha

/-- Two arrows that preserve the diagonal compose when the first interchanges with the second. -/
theorem pairArrows_copy_comp {X A B : τ} (f : obj X ⟶ obj A) (g : obj A ⟶ obj B)
    (central : WhiskerCentral f) (hf : pairArrows f f = f ≫ diagonalArrow A)
    (hg : pairArrows g g = g ≫ diagonalArrow B) :
    pairArrows (f ≫ g) (f ≫ g) = (f ≫ g) ≫ diagonalArrow B :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductCopy.pairArrows_copy_comp f g central hf hg

/-- Given primitive interchange, primitive copying is equivalent to copying and interchange for the sequential generators and their composites. -/
theorem primitiveReturnsCopy_iff_generated {ε : Type w} [HasEff Φ ε] (pe : ε)
    (central : PrimitiveReturnsCentral (τ := τ) (Φ := Φ) pe) :
    PrimitiveReturnsCopy (τ := τ) (Φ := Φ) pe ↔
      (PureReturnGenerators (τ := τ) (Φ := Φ) pe).multiplicativeClosure ≤ CentralCopies :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProductCopy.primitiveReturnsCopy_iff_generated pe central

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.ForwardingTables

/-! # Uniformity of finite forwarding tables -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ForwardingTables

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open UnitSumSquare (Shape)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Precomposing the assembled table with a row injection selects that row. -/
theorem inj_table (P : τ) (A : Shape) {X : Paper.TypeCategory (τ := τ) Φ}
    (rows : A.Row → (ofType P ⟶ X)) (i : A.Row) : inj P A i ≫ table P A rows = rows i :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTables.inj_table P A rows i

/-- The forwarding injections jointly determine a standard Paper arrow. -/
theorem hom_ext (P : τ) (A : Shape) {X : Paper.TypeCategory (τ := τ) Φ} {f g : obj P A ⟶ X}
    (h : ∀ i, inj P A i ≫ f = inj P A i ≫ g) : f = g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTables.hom_ext P A h

/-- Each row injection is admissible in Paper's constructor uniformity rule. -/
theorem inj_is_branch (P : τ) (A : Shape) (i : A.Row) :
    ∃ (a : Tm Φ) (ha : Tm.BranchValue [P] a (sumType P A)),
      inj P A i = ofRegion (.br (ℓ := 0) rfl ha) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTables.inj_is_branch P A i

/-- A binary test reflects equality of forwarded exit or recurrence tags. -/
theorem separate_output (P : τ) (hP : SeparatesTags (Φ := Φ) P) (B A : Shape)
    {x y : Sum B.Row A.Row} (h : projection.map (output (Φ := Φ) P B A x) =
      projection.map (output (Φ := Φ) P B A y)) : x = y :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTables.separate_output P hP B A h

/-- A pointwise tag square reconstructs the ordinary square in standard Paper. -/
theorem square_of_tags (P : τ) (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : ∀ i, (p i).map id tags = q (tags i)) :
    step (Φ := Φ) P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D tags) =
      stateMap P A D tags ≫ step P B D q :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTables.square_of_tags P B A D tags p q comm

/-- The projected square reflects to pointwise tags when the payload separates two injections. -/
theorem tags_of_projected_square (P : τ) (hP : SeparatesTags (Φ := Φ) P)
    (B A D : Shape) (tags : A.Row → D.Row) (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : projection.map (step (Φ := Φ) P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D tags)) =
      projection.map (stateMap P A D tags ≫ step P B D q)) :
    ∀ i, (p i).map id tags = q (tags i) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTables.tags_of_projected_square P hP B A D tags p q comm

/-- A coded tag square is uniform under iteration at any common payload type. -/
theorem iterate_of_tags (P : τ) (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : ∀ i, (p i).map id tags = q (tags i)) :
    iterate (step (Φ := Φ) P B A p) = stateMap P A D tags ≫ iterate (step P B D q) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTables.iterate_of_tags P B A D tags p q comm

/-- A projected square is uniform in standard Paper for a payload that
separates tags after projection or is already initial in standard Paper. -/
theorem iterate_of_projected_square (P : τ) (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (payload : SeparatesTags (Φ := Φ) P ∨ Nonempty (IsInitial (ofType (Φ := Φ) P)))
    (comm : projection.map (step (Φ := Φ) P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D tags)) =
      projection.map (stateMap P A D tags ≫ step P B D q)) :
    iterate (step (Φ := Φ) P B A p) = stateMap P A D tags ≫ iterate (step P B D q) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTables.iterate_of_projected_square P B A D tags p q payload comm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ForwardingTables

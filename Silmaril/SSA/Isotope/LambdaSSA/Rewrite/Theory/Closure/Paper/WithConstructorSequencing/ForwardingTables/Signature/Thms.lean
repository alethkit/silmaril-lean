module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Initial.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.ForwardingTablesSignature

/-! # Forwarding uniformity for arbitrary instruction signatures over free simple types -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ForwardingTables

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open UnitSumSquare (Shape)

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]

/-- Projection collapses the two binary tags exactly at structurally empty types. -/
theorem not_separatesTags_iff (P : Ty α) :
    (¬ SeparatesTags (Φ := Φ) P) ↔ Paper.StructurallyEmpty P :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesSignature.not_separatesTags_iff P

/-- Free simple types either separate tags or are initial, independently of the instruction signature. -/
theorem separates_or_initial_ofTy (P : Ty α) :
    SeparatesTags (Φ := Φ) P ∨ Nonempty (IsInitial (ofType (Φ := Φ) P)) := by
  classical
  exact em (SeparatesTags (Φ := Φ) P) |>.imp id fun h => ((not_separatesTags_iff P).mp h).initial

/-- The projected square suffices for standard Paper uniformity over any instruction signature
on free simple types. The rows and state map forward their common payload unchanged. -/
theorem iterate_of_signature_square (P : Ty α) (B A D : Shape)
    (tags : A.Row → D.Row) (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : projection.map (step (Φ := Φ) P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D tags)) =
      projection.map (stateMap P A D tags ≫ step P B D q)) :
    iterate (step (Φ := Φ) P B A p) = stateMap P A D tags ≫ iterate (step P B D q) :=
  iterate_of_projected_square P B A D tags p q (separates_or_initial_ofTy P) comm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ForwardingTables

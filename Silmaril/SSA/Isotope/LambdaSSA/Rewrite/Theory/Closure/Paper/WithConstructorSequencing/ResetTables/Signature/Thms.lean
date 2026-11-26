module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.ResetTablesSignature

/-! # Fixed-constructor reset uniformity for arbitrary instruction signatures -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open ForwardingTables (obj)
open UnitSumSquare (Shape StateCode OutputCode)

local notation "iterate" => Paper.TypeCategory.iterate

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]
  {P : Ty α} {w : Tm Φ} (hw : Tm.BranchValue [] w P)

/-- A closed constructor reset remains distinct from forwarding in the constructor-sequencing quotient. -/
theorem separatesActions : SeparatesActions hw :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesSignature.separatesActions hw

/-- Observing the fixed reset value distinguishes opposite sum tags after projection. -/
theorem separatesResetTags : SeparatesResetTags hw :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesSignature.separatesResetTags hw

/-- The projected square suffices for standard Paper uniformity. Each row
forwards the common payload or resets it to the same closed constructor. -/
theorem iterate_of_projected_square (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (comm : projection.map (step hw B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap hw A D rows)) =
      projection.map (stateMap hw A D rows ≫ step hw B D q)) :
    iterate (step hw B A p) = stateMap hw A D rows ≫ iterate (step hw B D q) :=
  iterate_of_codes hw B A D rows p q
    (codes_of_projected_square hw (separatesResetTags hw) (separatesActions hw) B A D rows p q comm)

/-- A commuting square in standard Paper also suffices. -/
theorem iterate_of_syntactic_square (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (comm : step hw B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap hw A D rows) =
      stateMap hw A D rows ≫ step hw B D q) :
    iterate (step hw B A p) = stateMap hw A D rows ≫ iterate (step hw B D q) :=
  iterate_of_projected_square hw B A D rows p q (congrArg projection.map comm)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables

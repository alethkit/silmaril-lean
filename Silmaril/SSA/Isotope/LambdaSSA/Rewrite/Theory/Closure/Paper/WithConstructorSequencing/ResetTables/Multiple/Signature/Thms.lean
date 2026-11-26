module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Multiple.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.ResetTablesMultipleSignature

/-! # Projected squares for finite tables with arbitrary closed resets -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables.Multiple

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open ForwardingTables (obj)
open UnitSumSquare (Shape)

local notation "iterate" => Paper.TypeCategory.iterate

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] (P : Ty α)

/-- Projection distinguishes forwarding and every different closed reset.
The test uses the observer for the constructor-sequencing relation. -/
theorem action_injective :
    Function.Injective (fun m : Option (ClosedValue Φ P) => projection.map (action P m)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleSignature.action_injective P

/-- Equal projected outputs have equal payload actions in standard Paper. -/
theorem row_action_eq_of_projected (B A : Shape) (x y : OutputCode (ClosedValue Φ P) B A)
    (equal : projection.map (output P B A x) = projection.map (output P B A y)) :
    action P x.reset = action P y.reset :=
  congrArg (action P) (action_injective P (projected_action_eq P B A x y equal))

/-- Reflect the ordinary commuting square from the constructor-sequencing quotient.
The initial-payload case uses standard Paper initiality. -/
theorem square_of_projected (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (q : D.Row → OutputCode (ClosedValue Φ P) B D)
    (comm : projection.map (step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows)) =
      projection.map (stateMap P A D rows ≫ step P B D q)) :
    step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows) =
      stateMap P A D rows ≫ step P B D q :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleSignature.square_of_projected P B A D rows p q comm

/-- Projected square uniformity in standard Paper for finite tables with arbitrary closed assignments. -/
theorem iterate_of_projected_square (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (q : D.Row → OutputCode (ClosedValue Φ P) B D)
    (comm : projection.map (step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows)) =
      projection.map (stateMap P A D rows ≫ step P B D q)) :
    iterate (step P B A p) = stateMap P A D rows ≫ iterate (step P B D q) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleSignature.iterate_of_projected_square P B A D rows p q comm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables.Multiple

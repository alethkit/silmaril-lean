module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Multiple.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.ResetTablesMultiple

/-! # Last assignments and uniformity of finite tables -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables.Multiple

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open ForwardingTables (obj inj)
open UnitSumSquare (Shape)

local notation "iterate" => Paper.TypeCategory.iterate

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] (P : τ)

/-- Composition performs exactly the last assignment, if any. -/
theorem action_comp (before after : Option (ClosedValue Φ P)) :
    action P before ≫ action P after = action P (thenReset before after) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultiple.action_comp P before after

/-- A state-map row is its payload action followed by its chosen injection. -/
theorem inj_stateMap (A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D) (i : A.Row) :
    inj P A i ≫ stateMap P A D rows = action P (rows i).reset ≫ inj P D (rows i).tag :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultiple.inj_stateMap P A D rows i

/-- A successful finite run supplies the exit tag and the last assignment to categorical iteration. -/
theorem iterate_run (B A : Shape) (p : A.Row → OutputCode (ClosedValue Φ P) B A)
    {n : Nat} {i : A.Row} {o : StateCode (ClosedValue Φ P) B} (h : run p n i = some o) :
    inj P A i ≫ iterate (step P B A p) = action P o.reset ≫ inj P B o.tag :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultiple.iterate_runWith P B A (inj P B) p h

/-- A row that never exits has the iteration of the singleton forwarding loop,
even if its transient path and cycle perform different assignments. -/
theorem iterate_nonexit_row (B A : Shape) (p : A.Row → OutputCode (ClosedValue Φ P) B A) (i : A.Row)
    (infinite : ¬ ReachesExit p i) :
    inj P A i ≫ iterate (step P B A p) =
      iterate (coprod.inr : ofType P ⟶ obj P B ⨿ ofType P) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultiple.iterate_nonexit_row P B A p i infinite

/-- A syntactic commuting square on coded rows gives uniformity in standard Paper. -/
theorem iterate_of_codes (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (q : D.Row → OutputCode (ClosedValue Φ P) B D)
    (square : ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).reset) :
    iterate (step P B A p) = stateMap P A D rows ≫ iterate (step P B D q) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultiple.iterate_of_codes P B A D rows p q square

/-- Interpret a code square as a standard Paper arrow equality. -/
theorem square_of_codes (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (q : D.Row → OutputCode (ClosedValue Φ P) B D)
    (square : ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).reset) :
    step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows) =
      stateMap P A D rows ≫ step P B D q :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultiple.square_of_codes P B A D rows p q square

/-- A projected square gives equality of the two composed outputs at each input row. -/
theorem projected_row_eq (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (q : D.Row → OutputCode (ClosedValue Φ P) B D)
    (comm : projection.map (step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows)) =
      projection.map (stateMap P A D rows ≫ step P B D q)) (i : A.Row) :
    projection.map (output P B D ((p i).mapState rows)) =
      projection.map (output P B D ((q (rows i).tag).withInput (rows i).reset)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultiple.projected_row_eq P B A D rows p q comm i

/-- Forgetting the output tag extracts the composed payload action after projection. -/
theorem projected_action_eq (B A : Shape) (x y : OutputCode (ClosedValue Φ P) B A)
    (agree : projection.map (output P B A x) = projection.map (output P B A y)) :
    projection.map (action P x.reset) = projection.map (action P y.reset) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultiple.projected_action_eq P B A x y agree

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables.Multiple

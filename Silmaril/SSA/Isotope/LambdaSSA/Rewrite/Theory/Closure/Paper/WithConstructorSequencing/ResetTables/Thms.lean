module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.ResetTables

/-! # Fixed constructor resets and mixed finite feedback -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open ForwardingTables (obj inj)
open UnitSumSquare (Shape Payload StateCode OutputCode)
open UnitSumSquare.Cycles.Payloads (ReachesExit)

local notation "iterate" => Paper.TypeCategory.iterate

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {P : τ} {w : Tm Φ} (hw : Tm.BranchValue [] w P)

/-- A finite composition of payload actions remembers whether a reset occurred. -/
theorem action_comp (left right : Payload) :
    action hw left ≫ action hw right = action hw (left.then right) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTables.action_comp hw left right

/-- Select the stored action and target of a state-map row. -/
theorem inj_stateMap (A D : Shape) (rows : A.Row → StateCode D) (i : A.Row) :
    inj P A i ≫ stateMap hw A D rows = action hw (rows i).payload ≫ inj P D (rows i).tag :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTables.inj_stateMap hw A D rows i

/-- Iteration absorbs either payload action before a singleton loop with no exits. -/
theorem action_before_self (Y : Paper.TypeCategory (τ := τ) Φ) (m : Payload) :
    action hw m ≫ iterate (coprod.inr : ofType P ⟶ Y ⨿ ofType P) =
      iterate (coprod.inr : ofType P ⟶ Y ⨿ ofType P) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTables.action_before_self hw Y m

/-- Iteration on a nonexiting row is the singleton nonexiting loop, regardless of its resets. -/
theorem iterate_nonexit_row (B A : Shape) (p : A.Row → OutputCode B A) (i : A.Row)
    (infinite : ¬ ReachesExit p i) :
    inj P A i ≫ iterate (step hw B A p) =
      iterate (coprod.inr : ofType P ⟶ obj P B ⨿ ofType P) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTables.iterate_nonexit_row hw B A p i infinite

/-- The syntactic code square implies categorical uniformity in standard Paper. -/
theorem iterate_of_codes (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (square : ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).payload) :
    iterate (step hw B A p) = stateMap hw A D rows ≫ iterate (step hw B D q) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTables.iterate_of_codes hw B A D rows p q square

/-- Interpret a commuting square of row codes in standard Paper. -/
theorem square_of_codes (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (square : ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).payload) :
    step hw B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap hw A D rows) =
      stateMap hw A D rows ≫ step hw B D q :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTables.square_of_codes hw B A D rows p q square

/-- The binary tag and payload tests jointly determine every coded row. -/
theorem separate_output (tags : SeparatesResetTags hw) (modes : SeparatesActions hw) (B A : Shape)
    {x y : OutputCode B A}
    (agree : projection.map (output hw B A x) = projection.map (output hw B A y)) : x = y :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTables.separate_output hw tags modes B A agree

/-- Recover the code square from equality after projection using the two binary tests. -/
theorem codes_of_projected_square (tags : SeparatesResetTags hw) (modes : SeparatesActions hw)
    (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (comm : projection.map (step hw B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap hw A D rows)) =
      projection.map (stateMap hw A D rows ≫ step hw B D q)) :
    ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).payload :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTables.codes_of_projected_square hw tags modes B A D rows p q comm

/-- If reset is identity in standard Paper, erase actions and use forwarding uniformity. -/
theorem iterate_when_reset_is_id (hId : action hw .literal = 𝟙 (ofType P))
    (B A D : Shape) (rows : A.Row → StateCode D) (p : A.Row → OutputCode B A)
    (q : D.Row → OutputCode B D)
    (payload : ForwardingTables.SeparatesTags (Φ := Φ) P ∨ Nonempty (IsInitial (ofType (Φ := Φ) P)))
    (comm : projection.map (step hw B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap hw A D rows)) =
      projection.map (stateMap hw A D rows ≫ step hw B D q)) :
    iterate (step hw B A p) = stateMap hw A D rows ≫ iterate (step hw B D q) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTables.iterate_when_reset_is_id hw hId B A D rows p q payload comm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables

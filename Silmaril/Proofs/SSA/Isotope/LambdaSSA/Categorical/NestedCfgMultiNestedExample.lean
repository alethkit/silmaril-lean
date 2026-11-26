module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.MultiNested.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
import Mathlib.Tactic.FinCases

/-! # Two independently written nested rows exchange tagged replies -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgMultiNestedExample

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open NestedAdmission (exits)
open NestedAdmission.Finite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private inductive Op where
  | poll
  | resume

private abbrev U : Ty Empty := .unit
private abbrev Pair : Ty Empty := .product U U

instance : HasTy Op (Ty Empty) where
  src
    | .poll => U
    | .resume => Pair
  trg
    | .poll => .coprod Pair U
    | .resume => .coprod U Pair

private def index : Fin 3 → Fin 4 := Fin.cases 0 (Fin.cases 2 (fun _ => 3))
private def keep : Fin 3 ↪ Fin 4 :=
  ⟨index, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

private def types : Fin 3 → Ty Empty := Fin.cases U (fun _ => Pair)
private def forms : Fin 3 → Bool := Fin.cases true (Fin.cases true (fun _ => false))

private def wide (D E dead : Ty Empty) : Fin 4 → Ty Empty :=
  Fin.cases (.coprod U D) (Fin.cases dead (Fin.cases (.coprod Pair E) (fun _ => Pair)))

private def outerGuard (body : Region Op) : Region Op :=
  .case (.var 0) (body.renameVars (Silmaril.DeBruijn.lift Nat.succ)) (.br 3 .unit)

private def first (wrong : Bool) : Region Op :=
  .cfg (.br 0 (.var 0)) 1 (fun _ =>
    .case (.op .poll (.var 0))
      (.br 2 (if wrong then .inr (.var 0) else .inl (.var 0))) (.br 4 (.var 0)))

private def second : Region Op :=
  .cfg (.br 0 (.var 0)) 1 (fun _ =>
    .case (.op .resume (.var 0)) (.br 1 (.inl (.var 0))) (.br 3 (.var 0)))

private def ordinary : Region Op :=
  .case (.op .resume (.var 0)) (.br 0 (.inl (.var 0))) (.br 4 (.var 0))

private def table (wrong : Bool) : CfgRestriction Op 4 :=
  ⟨.br 0 (.inl .unit), Fin.cases (outerGuard (first wrong))
    (Fin.cases (.br 3 .unit) (Fin.cases (outerGuard second) (fun _ => ordinary)))⟩

private abbrev graph (wrong : Bool) := (table wrong).source keep

private def plan : MultiNested.Plan Op 3 4 :=
  (MultiNested.check? keep types forms (graph false)).get (by decide)

/-- One step anchors the second nested payload. Its different reply
then anchors the ordinary slot. -/
example : (plan.anchors 0).contains 1 = false ∧ (plan.anchors 1).contains 1 = true ∧
    (plan.anchors 1).contains 2 = false ∧ (plan.anchors 2).contains 2 = true := by decide

private theorem entry_typed (wrong : Bool) (D E dead : Ty Empty) :
    ((table wrong).entry.renameLabels (retainLabelIndex keep)).HasType [] (List.ofFn (wide D E dead) ++ exits) :=
  (show (table wrong).entry.HasType [] (List.ofFn (fun i => wide D E dead (keep i)) ++ exits) from
    .br rfl (.inl .unit)).renameLabels (retainLabelRen keep _ _)

private theorem rows_typed (wrong : Bool) (D E dead : Ty Empty) (badType : wrong = true → E = Pair) (i : Fin 4) :
    (((table wrong).rows i).renameLabels (retainLabelIndex keep)).HasType
      [wide D E dead i] (List.ofFn (wide D E dead) ++ exits) := by
  let L := List.ofFn (fun i => wide D E dead (keep i)) ++ exits
  have row0 : (first wrong).HasType [U] L := by
    refine .cfg (fun _ => U) (.br rfl (.var rfl)) (fun _ => .case (.op (.var rfl)) ?_ (.br rfl (.var rfl)))
    cases wrong
    · exact .br rfl (.inl (.var rfl))
    · have eq := badType rfl
      subst E
      exact .br rfl (.inr (.var rfl))
  have row2 : second.HasType [Pair] L :=
    .cfg (fun _ => Pair) (.br rfl (.var rfl)) (fun _ =>
      .case (.op (.var rfl)) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl)))
  have guard {A T : Ty Empty} {body : Region Op} (typed : body.HasType [A] L) :
      (outerGuard body).HasType [.coprod A T] L :=
    .case (.var rfl) (typed.renameVars ((Ren.wk [] (.coprod A T)).lift A)) (.br rfl .unit)
  have deadRow : (Region.br 3 .unit : Region Op).HasType [dead] L := .br rfl .unit
  have ord : ordinary.HasType [Pair] L :=
    .case (.op (.var rfl)) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl))
  have ren := retainLabelRen keep (wide D E dead) exits
  exact Fin.cases ((guard row0).renameLabels ren)
    (Fin.cases (deadRow.renameLabels ren) (Fin.cases ((guard row2).renameLabels ren)
      (fun _ => ord.renameLabels ren))) i

/-- The wrong inter-nested tag survives exact typing and the outer target
restriction. The route checker returns unknown. -/
example : (graph true).HasType [] exits ∧ (CfgRestriction.check? keep exits.length (graph true)).isSome = true ∧
    MultiNested.compare? keep types forms (graph true) = .unknown :=
  ⟨.cfg (wide U Pair U) (entry_typed true U Pair U) (rows_typed true U Pair U (fun _ => rfl)), by decide, by decide⟩

private def replies (back : Bool) : Op → Value Empty → Nat → Value Empty → Nat → Prop
  | .poll, .unit, 0, .inl (.pair .unit .unit), 1 => True
  | .resume, .pair .unit .unit, 1, .inl .unit, 2 => back = true
  | .resume, .pair .unit .unit, 1, .inr (.pair .unit .unit), 2 => back = false
  | .poll, .unit, 2, .inr .unit, 3 => True
  | .resume, .pair .unit .unit, 2, .inr (.pair .unit .unit), 3 => True
  | _, _, _, _, _ => False

/-- Written slots zero and two exchange left-tagged transfers. -/
example : Semantics.Region.Eval (replies true) (fun _ => .unit) (graph false) 0 0 .unit 3 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .inl (.pair .unit .unit)) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 3) (by decide)
        (.case_inl (.op .var
          (show replies true Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro))
          (.br (.inl .var))) (.exit (by decide))))
  · refine .step (label := 2) (next := 0) (middle := .inl .unit) (s₁ := 2) (by decide) ?_ ?_
    · exact .case_inl .var (.cfg (.br .var)
        (.step (label := 0) (next := 1) (by decide)
          (.case_inl (.op .var
            (show replies true Op.resume (.pair .unit .unit) 1 (.inl .unit) 2 from rfl))
            (.br (.inl .var))) (.exit (by decide))))
    · refine .step (label := 0) (next := 4) (middle := .unit) (s₁ := 3) (by decide) ?_ (.exit (by decide))
      exact .case_inl .var (.cfg (.br .var)
        (.step (label := 0) (next := 5) (by decide)
          (.case_inr (.op .var
            (show replies true Op.poll .unit 2 (.inr .unit) 3 from True.intro)) (.br .var)) (.exit (by decide))))

/-- The second nested reply can instead enter ordinary slot three and take the pair exit. -/
example : Semantics.Region.Eval (replies false) (fun _ => .unit) (graph false) 0 1 (.pair .unit .unit) 3 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .inl (.pair .unit .unit)) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 3) (by decide)
        (.case_inl (.op .var
          (show replies false Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro))
          (.br (.inl .var))) (.exit (by decide))))
  · refine .step (label := 2) (next := 3) (middle := .pair .unit .unit) (s₁ := 2) (by decide) ?_ ?_
    · exact .case_inl .var (.cfg (.br .var)
        (.step (label := 0) (next := 4) (by decide)
          (.case_inr (.op .var
            (show replies false Op.resume (.pair .unit .unit) 1 (.inr (.pair .unit .unit)) 2 from rfl))
            (.br .var)) (.exit (by decide))))
    · exact .step (label := 3) (next := 5) (by decide)
        (.case_inr (.op .var
          (show replies false Op.resume (.pair .unit .unit) 2 (.inr (.pair .unit .unit)) 3 from True.intro))
          (.br .var)) (.exit (by decide))

/-- The wrong tag follows the same first request to slot two and takes its right arm. -/
example : Semantics.Region.Eval (replies true) (fun _ => .unit) (graph true) 0 0 .unit 1 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .inr (.pair .unit .unit)) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 3) (by decide)
        (.case_inl (.op .var
          (show replies true Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro))
          (.br (.inr .var))) (.exit (by decide))))
  · exact .step (label := 2) (next := 4) (by decide) (.case_inr .var (.br .unit)) (.exit (by decide))

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

/-- Both exact witnesses are of the original full graph. The inactive
summands of both nested slots and the omitted outer input type vary. -/
example (roll : IterationRolling C) :
    ∃ f g : Arrow,
      CfgDenotesAt J M (wide U Pair U) ((table false).entry.renameLabels (retainLabelIndex keep))
        (fun i => ((table false).rows i).renameLabels (retainLabelIndex keep)) f ∧
      CfgDenotesAt J M (wide .empty .empty .empty) ((table false).entry.renameLabels (retainLabelIndex keep))
        (fun i => ((table false).rows i).renameLabels (retainLabelIndex keep)) g ∧ f = g := by
  have never : (false : Bool) = true → False := by decide
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (wide U Pair U)
    (entry_typed false U Pair U) (rows_typed false U Pair U (fun _ => rfl))
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (wide .empty .empty .empty)
    (entry_typed false .empty .empty .empty) (rows_typed false .empty .empty .empty (fun h => (never h).elim))
  have tl : (graph false).HasType [] exits := .cfg (wide U Pair U)
    (entry_typed false U Pair U) (rows_typed false U Pair U (fun _ => rfl))
  have tr : (graph false).HasType [] exits := .cfg (wide .empty .empty .empty)
    (entry_typed false .empty .empty .empty) (rows_typed false .empty .empty .empty (fun h => (never h).elim))
  have dl : RegionDenotes J M tl f := left.denotes J M
  have dr : RegionDenotes J M tr g := right.denotes J M
  have ok : MultiNested.compare? keep types forms (graph false) = .certified := by decide
  exact ⟨f, g, left, right, MultiNested.compare?_sound J M roll ok dl dr⟩

end Model

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgMultiNestedExample

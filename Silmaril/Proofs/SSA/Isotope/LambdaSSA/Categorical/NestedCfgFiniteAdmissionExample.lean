module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms

/-! # Two heterogeneous inner states with an omitted middle slot -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgFiniteAdmissionExample

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open NestedAdmission (exits)

private inductive Op where
  | unitRequest
  | pairRequest

private abbrev U := NestedAdmission.unitTy
private abbrev Pair := NestedAdmission.pairTy
private abbrev tag (D : Ty Empty) : Ty Empty := .coprod U D
private abbrev slots (A : Ty Empty) : Fin 1 → Ty Empty := fun _ => A
private abbrev labels (A : Ty Empty) : LCtx (Ty Empty) := List.ofFn (slots A) ++ exits

instance : HasTy Op (Ty Empty) where
  src
    | .unitRequest => U
    | .pairRequest => Pair
  trg
    | .unitRequest => .coprod Pair (.coprod U U)
    | .pairRequest => .coprod U Pair

private def keep : Fin 2 ↪ Fin 3 :=
  ⟨fun i => ⟨2 * i.val, by omega⟩, by
    intro i j h
    have eq := congrArg Fin.val h
    apply Fin.ext
    change 2 * i.val = 2 * j.val at eq
    omega⟩

private def types : Fin 2 → Ty Empty := Fin.cases U (fun _ => Pair)
private def family (dead : Ty Empty) : Fin 3 → Ty Empty := Fin.cases U (Fin.cases dead (fun _ => Pair))

private def innerEntry : Region Op := .br 0 (.var 0)

private def fromUnit (next : Region Op) : Region Op :=
  .case (.op .unitRequest (.var 0)) next
    (.case (.var 0) (.br 2 (.inl (.var 0))) (.br 3 (.var 0)))

private def fromPair : Region Op :=
  .case (.op .pairRequest (.var 0)) (.br 0 (.var 0)) (.br 4 (.var 0))

private def dead : Region Op := .br 3 .unit

private def actualEntry : Region Op := innerEntry.renameLabels (retainLabelIndex keep)

private def rows (bad : Bool) : Fin 3 → Region Op :=
  Fin.cases (if bad then
    .case (.op .unitRequest (.var 0)) (.br 1 .unit)
      (.case (.var 0) (.br 3 (.inl (.var 0))) (.br 4 (.var 0)))
    else (fromUnit (.br 1 (.var 0))).renameLabels (retainLabelIndex keep))
    (Fin.cases (dead.renameLabels (retainLabelIndex keep)) (fun _ => fromPair.renameLabels (retainLabelIndex keep)))

private def guarded (body : Region Op) : Region Op :=
  .case (.var 0) (body.renameVars (Silmaril.DeBruijn.lift Nat.succ)) (.br 0 (.var 1))

private def outerRow (bad : Bool) : Region Op := guarded (.cfg actualEntry 3 (rows bad))
private def start : Region Op := .br 0 (.inl .unit)
private def original (bad : Bool) : Region Op := .cfg start 1 (fun _ => outerRow bad)

private theorem actualEntry_typed (D deadTy : Ty Empty) :
    actualEntry.HasType [U] (List.ofFn (family deadTy) ++ labels (tag D)) :=
  (show innerEntry.HasType [U] (List.ofFn (fun i => family deadTy (keep i)) ++ labels (tag D)) from
    .br rfl (.var rfl)).renameLabels (retainLabelRen keep _ _)

private theorem row_typed (D deadTy : Ty Empty) (i : Fin 3) :
    (rows false i).HasType [family deadTy i, U] (List.ofFn (family deadTy) ++ labels (tag D)) := by
  let L := List.ofFn (fun i => family deadTy (keep i)) ++ labels (tag D)
  have ren := retainLabelRen keep (family deadTy) (labels (tag D))
  have h0 : (fromUnit (.br 1 (.var 0))).HasType [U, U] L :=
    .case (.op (.var rfl)) (.br rfl (.var rfl))
      (.case (.var rfl) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl)))
  have h1 : dead.HasType [deadTy, U] L := .br rfl .unit
  have h2 : fromPair.HasType [Pair, U] L :=
    .case (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.var rfl))
  exact Fin.cases (h0.renameLabels ren)
    (Fin.cases (h1.renameLabels ren) (fun _ => h2.renameLabels ren)) i

private theorem outer_typed (bad : Bool) (D deadTy : Ty Empty) (allowed : bad = true → deadTy = U) :
    (outerRow bad).HasType [tag D] (labels (tag D)) := by
  have inner : (Region.cfg actualEntry 3 (rows bad)).HasType [U] (labels (tag D)) := by
    refine .cfg (family deadTy) (actualEntry_typed D deadTy) ?_
    cases bad
    · exact row_typed D deadTy
    · rw [allowed rfl]
      intro i
      refine Fin.cases ?_ (fun j => row_typed D U j.succ) i
      exact .case (.op (.var rfl)) (.br rfl .unit)
        (.case (.var rfl) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl)))
  exact .case (.var rfl) (inner.renameVars ((Ren.wk [] (tag D)).lift U)) (.br rfl (.var rfl))

/-- The first request can name the omitted middle slot. Its exact typing
survives, but the finite comparison reports unknown. -/
example : (original true).HasType [] exits ∧
    NestedAdmission.Finite.compare? keep types (original true) = .unknown :=
  ⟨.cfg (slots (tag U)) (.br rfl (.inl .unit)) (fun _ => outer_typed true U U (fun _ => rfl)), by decide⟩

private def replies : Op → Value Empty → Nat → Value Empty → Nat → Prop
  | .unitRequest, .unit, 0, .inl (.pair .unit .unit), 1 => True
  | .pairRequest, .pair .unit .unit, 1, .inl .unit, 2 => True
  | .unitRequest, .unit, 2, .inr (.inr .unit), 3 => True
  | _, _, _, _, _ => False

/-- The original inner graph visits slots zero, two, and zero in sequence
before taking the first actual exit. The two payloads cross both requests. -/
example : Semantics.Region.Eval replies (fun _ => .unit) (.cfg actualEntry 3 (rows false)) 0 1 .unit 3 := by
  refine .cfg (.br .var) ?_
  refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl (.op .var (by trivial)) (.br .var)
  · refine .step (label := 2) (next := 0) (middle := .unit) (s₁ := 2) (by decide) ?_ ?_
    · exact .case_inl (.op .var (by trivial)) (.br .var)
    · refine .step (label := 0) (next := 4) (middle := .unit) (s₁ := 3) (by decide) ?_ (.exit (by decide))
      exact .case_inr (.op .var (by trivial)) (.case_inr .var (.br .var))

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

/-- Both original exact witnesses retain slots zero and two. Their requests
consume Unit and Unit × Unit respectively and can transfer to the other
retained slot. The omitted middle type and the outer right summand vary. -/
example (roll : IterationRolling C) :
    ∃ f g : Arrow,
      CfgDenotesAt J M (slots (tag U)) start (fun _ => outerRow false) f ∧
      CfgDenotesAt J M (slots (tag .empty)) start (fun _ => outerRow false) g ∧ f = g := by
  have rowLeft := outer_typed false U U (by intro h; cases h)
  have rowRight := outer_typed false .empty .empty (by intro h; cases h)
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (slots (tag U))
    (.br rfl (.inl .unit) : start.HasType [] (labels (tag U))) (fun _ => rowLeft)
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (slots (tag .empty))
    (.br rfl (.inl .unit) : start.HasType [] (labels (tag .empty))) (fun _ => rowRight)
  have ok : NestedAdmission.Finite.compare? keep types (original false) = .certified := by decide
  have typedLeft : (original false).HasType [] exits :=
    .cfg (slots (tag U)) (.br rfl (.inl .unit)) (fun _ => rowLeft)
  have typedRight : (original false).HasType [] exits :=
    .cfg (slots (tag .empty)) (.br rfl (.inl .unit)) (fun _ => rowRight)
  have dl : RegionDenotes J M typedLeft f := left.denotes J M
  have dr : RegionDenotes J M typedRight g := right.denotes J M
  exact ⟨f, g, left, right, NestedAdmission.Finite.compare?_sound J M roll ok dl dr⟩

end Model

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgFiniteAdmissionExample

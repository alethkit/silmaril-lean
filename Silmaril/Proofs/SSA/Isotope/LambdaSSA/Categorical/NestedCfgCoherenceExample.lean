module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Paths.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.BlockParameters.Thms

/-! # An inner native loop dispatching to an outer block or exit -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgFixture

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open UnusedSummand.BlockParameters
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

private inductive Op where
  | load
  | inspect

private abbrev U : Ty Empty := Silmaril.unit
private abbrev Flag : Ty Empty := Silmaril.coprod U U
private abbrev Reply : Ty Empty := Silmaril.coprod U Flag
private abbrev Result : Ty Empty := Silmaril.product U Flag
private abbrev exits : LCtx (Ty Empty) := [U, Result]

instance : HasTy Op (Ty Empty) where
  src
    | .load => U
    | .inspect => Flag
  trg
    | .load => Flag
    | .inspect => Reply

instance : HasEff Op Bool := ⟨fun _ => true⟩

private def outerFamilyAt (sibling : Ty Empty) : Fin 2 → Ty Empty :=
  Fin.cases Flag (fun _ => sibling)

private abbrev outerFamily := outerFamilyAt Result

private def innerFamily (dead : Ty Empty) : Fin 3 → Ty Empty :=
  Fin.cases Flag (Fin.cases Flag (fun _ => dead))

private abbrev outerLabels := List.ofFn outerFamily ++ exits

private def inner : Program (Φ := Op) (innerFamily U) outerLabels [Flag, U] where
  entry := .jump 0 (.var 0 rfl)
  blocks := Fin.cases
    (.parameter (.jump 1 (.var 0 rfl)))
    (Fin.cases
      (.parameter (.case (.op Op.inspect (.var 0 rfl))
        (.jump 0 (.var 1 rfl))
        (.case (.var 0 rfl)
          (.exit 1 rfl (.pair (.var 4 rfl) (.var 2 rfl)))
          (.exit 2 rfl (.var 0 rfl)))))
      (fun _ => .captured (.exit 2 rfl .unit)))

private def innerEntry : Region Op := .br 0 (.var 0)

private def innerRows : Fin 3 → Region Op := Fin.cases (.br 1 (.var 0))
  (Fin.cases
    (.case (.op Op.inspect (.var 0)) (.br 0 (.var 1))
      (.case (.var 0) (.br 4 (.pair (.var 4) (.var 2))) (.br 5 (.var 0))))
    (fun _ => .br 5 .unit))

private abbrev innerRegion : Region Op := .cfg innerEntry 3 innerRows

private theorem inner_written : inner.region = innerRegion := by
  change inner.region = .cfg innerEntry 3 innerRows
  unfold Program.region inner innerRows
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i

private theorem reachesFirst : inner.Reaches 0 := .entry rfl

private theorem reachesSecond : inner.Reaches 1 := .next reachesFirst rfl

private theorem inner_targets {i : Fin 3} (hit : inner.targets i) : i = 0 ∨ i = 1 := by
  rcases hit with hit | ⟨j, hit⟩
  · exact .inl (show (0 : Fin 3) = i from hit).symm
  · revert hit
    refine Fin.cases ?_ (Fin.cases ?_ (fun _ h => h.elim)) j
    · exact fun h => .inr (show (1 : Fin 3) = i from h).symm
    · rintro (h | h)
      · exact .inl (show (0 : Fin 3) = i from h).symm
      · rcases h with h | h <;> exact h.elim

private theorem closed : inner.ReachableParameters where
  targets _ hit := by
    rcases inner_targets hit with rfl | rfl
    · exact reachesFirst
    · exact reachesSecond
  parameters i :=
    Fin.cases (fun _ => reachesFirst) (Fin.cases (fun _ => reachesSecond) (fun _ h => h.elim)) i

private theorem innerEntry_typed (D : Ty Empty) :
    innerEntry.HasType [Flag, U] (List.ofFn (innerFamily D) ++ outerLabels) :=
  .br rfl (.var rfl)

private theorem innerRows_typed (D : Ty Empty) (i : Fin 3) :
    (innerRows i).HasType (innerFamily D i :: [Flag, U]) (List.ofFn (innerFamily D) ++ outerLabels) :=
  Fin.cases (.br rfl (.var rfl))
    (Fin.cases
      (.case (.op (.var rfl)) (.br rfl (.var rfl))
        (.case (.var rfl) (.br rfl (.pair (.var rfl) (.var rfl))) (.br rfl (.var rfl))))
      (fun _ => .br rfl .unit)) i

private def outerEntry : Region Op := .br 0 (.op Op.load (.var 0))
private def outerRows : Fin 2 → Region Op :=
  Fin.cases innerRegion (fun _ => .br 3 (.pair (.var 1) (.inl .unit)))
private abbrev outerRegion : Region Op := .cfg outerEntry 2 outerRows

private theorem outerEntry_typed_at (A : Ty Empty) :
    outerEntry.HasType [U] (List.ofFn (outerFamilyAt A) ++ exits) := .br rfl (.op (.var rfl))

private theorem sibling_typed_at (A : Ty Empty) :
    (outerRows 1).HasType [A, U] (List.ofFn (outerFamilyAt A) ++ exits) :=
  .br rfl (.pair (.var rfl) (.inl .unit))

private theorem outerEntry_typed : outerEntry.HasType [U] outerLabels := outerEntry_typed_at Result

private theorem outerRows_typed (D : Ty Empty) (i : Fin 2) :
    (outerRows i).HasType (outerFamily i :: [U]) outerLabels :=
  Fin.cases (.cfg (innerFamily D) (innerEntry_typed D) (innerRows_typed D))
    (fun _ => sibling_typed_at Result) i

/-- The outer entry and sibling block allow any sibling input type. -/
example (A : Ty Empty) :
    outerEntry.HasType [U] (List.ofFn (outerFamilyAt A) ++ exits) ∧
      (outerRows 1).HasType [A, U] (List.ofFn (outerFamilyAt A) ++ exits) :=
  ⟨outerEntry_typed_at A, sibling_typed_at A⟩

private theorem outerFamily_determined : LabelsDetermined [U] exits outerEntry outerRows outerFamily := by
  intro S he hb
  have first : S 0 = Flag := by
    cases he with
    | br target arg =>
        have label : At (List.ofFn S ++ exits) 0 (S 0) := by simp [At]
        cases arg
        exact Option.some.inj (label.symm.trans target)
  have nested : inner.region.HasType [Flag, U] (List.ofFn S ++ exits) := by
    rw [inner_written]
    simpa only [first] using
      (show innerRegion.HasType (S 0 :: [U]) (List.ofFn S ++ exits) from hb 0)
  have second : S 1 = Result :=
    inner.enclosing_type_at_reached reachesSecond (1 : Fin 2) (.inr (.inl ⟨rfl, rfl⟩)) nested
  funext i
  refine Fin.cases first (Fin.cases second ?_) i
  intro j
  exact Fin.elim0 j

private theorem innerDead_differs : innerFamily U 2 ≠ innerFamily .empty 2 := by
  intro eq
  cases eq

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

private theorem outer_functional (roll : IterationRolling C) :
    RegionDenotes.Functional J M [U] outerRegion exits := by
  apply RegionDenotes.Functional.cfg J M outerFamily_determined
  · exact (DeterminedRegion.br rfl (.op (.var rfl))).functional J M
  · intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · change RegionDenotes.Functional J M [Flag, U] innerRegion outerLabels
      rw [← inner_written]
      exact fun {_ _ _ _} d e => inner.denotes_eq J M roll closed d e
    · exact (DeterminedRegion.br rfl (.pair (.var rfl) (.inl .unit))).functional J M

local notation "Arrow" => J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M exits)

private def NestedAt (dead : Ty Empty) (f : Arrow) : Prop :=
  ∃ (entry : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M outerLabels))
    (rows : ∀ i, J.obj (ctxObj M (outerFamily i :: [U])) ⟶ J.obj (labelObj M outerLabels))
    (dispatch : J.obj (ctxObj M [U] ⊗ finiteLabelObj M outerFamily) ⟶ J.obj (labelObj M outerLabels)),
    RegionDenotes J M outerEntry_typed entry ∧
      CfgDenotesAt J M (innerFamily dead) innerEntry innerRows (rows 0) ∧
      RegionDenotes J M (outerRows_typed dead 1) (rows 1) ∧
      CollectiveDenotes J M [U] outerFamily exits rows dispatch ∧
      f = cfgDispatchArrow J M outerFamily entry dispatch

private theorem nested_exists (D : Ty Empty) : ∃ f : Arrow, NestedAt J M D f := by
  obtain ⟨innerArrow, exactInner⟩ := CfgDenotesAt.exists_of_typing J M (innerFamily D)
    (innerEntry_typed D) (innerRows_typed D)
  let rows (i : Fin 2) : J.obj (ctxObj M (outerFamily i :: [U])) ⟶ J.obj (labelObj M outerLabels) :=
    Fin.cases innerArrow (fun _ => denoteRegion J M (outerRows_typed D 1)) i
  obtain ⟨dispatch, blocks⟩ := collective_exists J M 1 [U] outerFamily (labelObj M outerLabels) rows
  exact ⟨_, _, rows, dispatch, denoteRegion_spec J M outerEntry_typed, exactInner,
    denoteRegion_spec J M (outerRows_typed D 1), ⟨blocks⟩, rfl⟩

private theorem NestedAt.denotes {D : Ty Empty} {f : Arrow} (w : NestedAt J M D f) :
    RegionDenotes J M (.cfg outerFamily outerEntry_typed (outerRows_typed D)) f := by
  obtain ⟨entry, rows, dispatch, de, di, dr, dc, eq⟩ := w
  apply CfgDenotesAt.denotes J M (R := outerFamily)
  refine ⟨outerEntry_typed, outerRows_typed D, entry, rows, dispatch, de, ?_, dc, eq⟩
  intro i
  refine Fin.cases (di.denotes J M) (Fin.cases dr ?_) i
  intro j
  exact Fin.elim0 j

/-- The inner entry supplies a flag that block 0 forwards to block 1.
An inspect reply can repeat, transfer that flag paired with the ambient
capture to outer block 1, or take outward label 0 directly. The sibling
block supplies a fixed pair payload at outward label 1. Its input type
comes from the inner transfer. The two exact witnesses have different
types at the untargeted inner slot. -/
example (roll : IterationRolling C) :
    innerFamily U 2 ≠ innerFamily .empty 2 ∧
      ∃ f g : Arrow, NestedAt J M U f ∧ NestedAt J M .empty g ∧ f = g := by
  obtain ⟨f, left⟩ := nested_exists J M U
  obtain ⟨g, right⟩ := nested_exists J M .empty
  exact ⟨innerDead_differs, f, g, left, right,
    outer_functional J M roll (left.denotes J M) (right.denotes J M)⟩

end Model

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgFixture

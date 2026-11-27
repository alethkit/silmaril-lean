module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation denoteRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetSeq.StraightLine.Structural (Slot Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetSeq.StraightLine.Structural Tagged

/-! ## Four ordered exits with product payloads

There is one atom. The primitive takes one atom and replies with one atom
under the left or the right tag. Two older atoms are captured. The exits
are a pair of atoms, one atom, a pair of atoms again, and the unit. The
first and the third exit have the same product type. -/

private inductive Probe | probe

local instance : TaggedSignature Unit Probe := ⟨fun _ => .atom (), fun _ => (), fun _ => ()⟩

private abbrev tok : Ty Unit := .base ()
private abbrev pairTy : Ty Unit := .product tok tok
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Probe n

private theorem separable : Separable older := separable_atoms (.snoc (.snoc .nil ()) ())

private abbrev exits : List (Ty Unit) := [pairTy, tok, pairTy, .unit]
private abbrev pairFirst : ExitAt exits pairTy := .here
private abbrev single : ExitAt exits tok := .there .here
private abbrev pairLater : ExitAt exits pairTy := .there (.there .here)
private abbrev finished : ExitAt exits .unit := .there (.there (.there .here))

example : pairFirst.index = 0 ∧ single.index = 1 ∧ pairLater.index = 2 ∧ finished.index = 3 := ⟨rfl, rfl, rfl, rfl⟩

/-- The same pair of tokens at the two exits of the product type gives two
different values. -/
example (x y : Nat × Nat) : pairFirst.value x ≠ pairLater.value y := fun same => by
  obtain ⟨-, -, position⟩ := ExitAt.value_inj pairFirst pairLater x y same
  exact absurd position (by decide)

private abbrev earlier : Slot older tok := ⟨1, rfl⟩
private abbrev later : Slot older tok := ⟨0, rfl⟩
private abbrev armCtx : BoundCtx (Ty Unit) 3 := older.snoc tok
private abbrev payload : Slot armCtx tok := ⟨0, rfl⟩
private abbrev innerCtx : BoundCtx (Ty Unit) 4 := armCtx.snoc tok
private abbrev fresh : Slot innerCtx tok := ⟨0, rfl⟩
private abbrev outer : Slot innerCtx tok := ⟨1, rfl⟩
private abbrev earlierDeep : Slot innerCtx tok := ⟨3, rfl⟩

/-! ## Leaves -/

/-- Return the two captures, in their order, at the first product exit. -/
private def both : CaseTree older exits (.inl (.pair (.bv 1) (.bv 0)) : Term 2) :=
  .ret pairFirst (.pair (.atom earlier) (.atom later))

/-- The same product at the later exit of the same type. -/
private def bothLater : CaseTree older exits (.inr (.inr (.inl (.pair (.bv 1) (.bv 0)))) : Term 2) :=
  .ret pairLater (.pair (.atom earlier) (.atom later))

/-- The same exit with the two components in the other order. -/
private def swapped : CaseTree older exits (.inl (.pair (.bv 0) (.bv 1)) : Term 2) :=
  .ret pairFirst (.pair (.atom later) (.atom earlier))

/-- The same exit with the second component changed. -/
private def doubled : CaseTree older exits (.inl (.pair (.bv 1) (.bv 1)) : Term 2) :=
  .ret pairFirst (.pair (.atom earlier) (.atom earlier))

/-! ## A nested request returning a product

Probe the earlier capture, then under the left tag probe the payload. The
inner left arm returns, at the first product exit, the fresh reply atom
paired with the earlier capture. The other arms leave by the atom exit
and the unit exit. -/

private def deep : CaseTree older exits
    (.case (.op Probe.probe (.bv 1))
      (.case (.op Probe.probe (.bv 0)) (.inl (.pair (.bv 0) (.bv 3))) (.inr (.inl (.bv 1))))
      (.inr (.inr (.inr (.inl .unit)))) : Term 2) :=
  .ask Probe.probe (.atom earlier)
    (.ask Probe.probe (.atom payload) (.ret pairFirst (.pair (.atom fresh) (.atom earlierDeep)))
      (.ret single (.atom outer)))
    (.ret finished .unit)

/-- The same tree with the two components of the product exchanged. -/
private def deepOrder : CaseTree older exits
    (.case (.op Probe.probe (.bv 1))
      (.case (.op Probe.probe (.bv 0)) (.inl (.pair (.bv 3) (.bv 0))) (.inr (.inl (.bv 1))))
      (.inr (.inr (.inr (.inl .unit)))) : Term 2) :=
  .ask Probe.probe (.atom earlier)
    (.ask Probe.probe (.atom payload) (.ret pairFirst (.pair (.atom earlierDeep) (.atom fresh)))
      (.ret single (.atom outer)))
    (.ret finished .unit)

/-- The same tree with the fresh reply atom replaced by the outer payload. -/
private def deepComponent : CaseTree older exits
    (.case (.op Probe.probe (.bv 1))
      (.case (.op Probe.probe (.bv 0)) (.inl (.pair (.bv 1) (.bv 3))) (.inr (.inl (.bv 1))))
      (.inr (.inr (.inr (.inl .unit)))) : Term 2) :=
  .ask Probe.probe (.atom earlier)
    (.ask Probe.probe (.atom payload) (.ret pairFirst (.pair (.atom outer) (.atom earlierDeep)))
      (.ret single (.atom outer)))
    (.ret finished .unit)

/-- The same tree with the same product returned at the later product exit. -/
private def deepExit : CaseTree older exits
    (.case (.op Probe.probe (.bv 1))
      (.case (.op Probe.probe (.bv 0)) (.inr (.inr (.inl (.pair (.bv 0) (.bv 3))))) (.inr (.inl (.bv 1))))
      (.inr (.inr (.inr (.inl .unit)))) : Term 2) :=
  .ask Probe.probe (.atom earlier)
    (.ask Probe.probe (.atom payload) (.ret pairLater (.pair (.atom fresh) (.atom earlierDeep)))
      (.ret single (.atom outer)))
    (.ret finished .unit)

/-! ## The ranked sentences are at the four original exits -/

private abbrev sentence {t u : Term 2} (p : CaseTree older exits t) (q : CaseTree older exits u) :
    RankedEquation (atomSig Unit Probe) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

example : (sentence both bothLater).1.exits = [pairTy, tok, pairTy, .unit] := rfl

/-- The region emitted from the read-back graph has the four ordered exits. -/
example : Region.HasType older.toList deep.graph.toSSA [pairTy, tok, pairTy, .unit] := deep.graph.toSSA_hasType

/-! ## A changed exit alone -/

private theorem exit_apart : ¬ RankedValid false (sentence both bothLater) := fun valid => by
  have same := (rankedValid_caseTree_iff separable both bothLater).mp valid
  simp at same

/-- The ordered-exit arrows of the two graphs differ at the ordered trace
model with atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf both.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf bothLater.graph) :=
  fun same => by
    have terms := (denoteRanked_caseTree_iff separable both bothLater).mp same
    simp at terms

/-- The model rejects the sentence. -/
example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Probe))
    (atomSig Unit Probe)).Sat (atomTraceRanked Unit Probe) (sentence both bothLater) := fun holds =>
  exit_apart ((rankedValid_branching_iff_atomTrace separable (entryOf both.graph)
    (entryOf bothLater.graph) (branching_graph both) (branching_graph bothLater)).mpr holds)

/-- In the nested arm: the same product at the later exit of its type. -/
example : ¬ RankedValid false (sentence deep deepExit) := fun valid => by
  have same := (rankedValid_caseTree_iff separable deep deepExit).mp valid
  simp at same

/-! ## A changed product alone, at an unchanged exit -/

/-- The order of the two components. -/
example : ¬ RankedValid false (sentence both swapped) := fun valid => by
  have same := (rankedValid_caseTree_iff separable both swapped).mp valid
  simp at same

/-- One component. -/
example : ¬ RankedValid false (sentence both doubled) := fun valid => by
  have same := (rankedValid_caseTree_iff separable both doubled).mp valid
  simp at same

/-- In the nested arm: the order of the fresh reply atom and the capture. -/
example : ¬ RankedValid false (sentence deep deepOrder) := fun valid => by
  have same := (rankedValid_caseTree_iff separable deep deepOrder).mp valid
  simp at same

/-- In the nested arm: the fresh reply atom replaced by the outer payload. -/
example : ¬ RankedValid false (sentence deep deepComponent) := fun valid => by
  have same := (rankedValid_caseTree_iff separable deep deepComponent).mp valid
  simp at same

/-- The ordered-exit arrows differ for the changed order as well. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf deep.graph) ≠
    denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf deepOrder.graph) :=
  fun same => by
    have terms := (denoteRanked_caseTree_iff separable deep deepOrder).mp same
    simp at terms

/-! ## The leaf reflection at one environment

Two leaves with the same traces at a separating environment have the same
exit position. The two leaves at the two product exits do not. -/

example (ρ : Isotope.Semantics.BoundEnv (LetSeq.StraightLine.Structural.Value (α := Unit)) older) (k : Nat)
    (sep : LetSeq.StraightLine.Structural.Separates ρ (Set.Iio k)) :
    LetCase.Structural.Reply.run both.typing ρ ≠ LetCase.Structural.Reply.run bothLater.typing ρ := fun same => by
  obtain ⟨-, -, position⟩ := ret_eq_of_run (Φ := Probe) pairFirst pairLater
    (.pair (.atom earlier) (.atom later)) (.pair (.atom earlier) (.atom later)) ρ sep same
  exact absurd position (by decide)

/-! ## A valid sentence at the four exits

The second graph is read back from the operand emitted by the first. -/

private def deepAgain : CheckedTable Probe older exits :=
  CheckedTable.ofLetCase (List.cons_ne_nil _ _) deep.graph.toLetCase.2

private theorem again_branching : Branching (emitted (P := atomSig Unit Probe) (entryOf deepAgain)) :=
  Branching.congr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) deep.graph.toLetCase.2)
    (branching_graph deep)

private theorem again_valid : RankedValid false (sentenceOf (entryOf deep.graph) (entryOf deepAgain)) :=
  (rankedValid_branching_iff separable (entryOf deep.graph) (entryOf deepAgain) (branching_graph deep)
    again_branching).mpr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) deep.graph.toLetCase.2).symm

/-- The two graphs have the same ordered-exit arrow at the ordered trace
model with atoms. -/
example : denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf deep.graph) =
    denoteRanked (traceJ (α := Unit) (Φ := Probe)) (atomTraceModel Unit Probe) (entryOf deepAgain) :=
  (rankedValid_branching_iff_atomTrace separable (entryOf deep.graph) (entryOf deepAgain)
    (branching_graph deep) again_branching).mp again_valid

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

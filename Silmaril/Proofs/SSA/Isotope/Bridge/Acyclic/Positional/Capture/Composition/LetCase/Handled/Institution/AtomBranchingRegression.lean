module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetSeq.StraightLine.Structural (Slot Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetSeq.StraightLine.Structural Tagged

/-! ## A tagged signature

There is one atom. The primitive takes one atom and replies with one atom
under the left or the right tag. Two older atoms are captured. -/

private inductive Probe | probe

local instance : TaggedSignature Unit Probe := ⟨fun _ => .atom (), fun _ => (), fun _ => ()⟩

private abbrev tok : Ty Unit := .base ()
private abbrev older : BoundCtx (Ty Unit) 2 := (BoundCtx.snoc .nil tok).snoc tok
private abbrev Term (n : Nat) := LetCase.LocallyNameless.Tm Empty Probe n

private theorem olderAtoms : AtomContext older := .snoc (.snoc .nil ()) ()
private theorem separable : Separable older := separable_atoms olderAtoms

example : instrTrg (τ := Ty Unit) Probe.probe = .coprod tok tok := rfl

/-- The earlier and the later of the two older captures. -/
private abbrev earlier : Slot older tok := ⟨1, rfl⟩
private abbrev later : Slot older tok := ⟨0, rfl⟩

/-- Under one arm: the payload, and the two older captures still in scope. -/
private abbrev armCtx : BoundCtx (Ty Unit) 3 := older.snoc tok
private abbrev payload : Slot armCtx tok := ⟨0, rfl⟩
private abbrev earlierIn : Slot armCtx tok := ⟨2, rfl⟩
private abbrev laterIn : Slot armCtx tok := ⟨1, rfl⟩

/-! ## Case trees -/

/-- Probe the earlier capture. Return the payload under the left tag and
the earlier capture under the right tag. -/
private def keep : CaseTree older () (.case (.op Probe.probe (.bv 1)) (.inl (.bv 0)) (.inl (.bv 2)) : Term 2) :=
  .ask Probe.probe (.atom earlier) (.ret payload) (.ret earlierIn)

/-- The same request with the two arms exchanged. -/
private def flip : CaseTree older () (.case (.op Probe.probe (.bv 1)) (.inl (.bv 2)) (.inl (.bv 0)) : Term 2) :=
  .ask Probe.probe (.atom earlier) (.ret earlierIn) (.ret payload)

/-- The same request, returning the payload under both tags. -/
private def both : CaseTree older () (.case (.op Probe.probe (.bv 1)) (.inl (.bv 0)) (.inl (.bv 0)) : Term 2) :=
  .ask Probe.probe (.atom earlier) (.ret payload) (.ret payload)

/-- The same arms after probing the later capture. -/
private def other : CaseTree older () (.case (.op Probe.probe (.bv 0)) (.inl (.bv 0)) (.inl (.bv 2)) : Term 2) :=
  .ask Probe.probe (.atom later) (.ret payload) (.ret earlierIn)

/-- Two arms deep: the outer payload, the inner payload and both older
captures are in scope. -/
private abbrev innerCtx : BoundCtx (Ty Unit) 4 := armCtx.snoc tok

/-- Probe the earlier capture, then under the left tag probe the payload
just received. The inner arms return the inner and the outer payload. -/
private def chain : CaseTree older ()
    (.case (.op Probe.probe (.bv 1)) (.case (.op Probe.probe (.bv 0)) (.inl (.bv 0)) (.inl (.bv 1)))
      (.inl (.bv 0)) : Term 2) :=
  .ask Probe.probe (.atom earlier)
    (.ask Probe.probe (.atom payload) (.ret (β := innerCtx) ⟨0, rfl⟩) (.ret (β := innerCtx) ⟨1, rfl⟩))
    (.ret payload)

/-- Probe the earlier capture and then the later one. -/
private def earlierFirst : CaseTree older ()
    (.case (.op Probe.probe (.bv 1)) (.case (.op Probe.probe (.bv 1)) (.inl (.bv 0)) (.inl (.bv 1)))
      (.inl (.bv 0)) : Term 2) :=
  .ask Probe.probe (.atom earlier)
    (.ask Probe.probe (.atom laterIn) (.ret (β := innerCtx) ⟨0, rfl⟩) (.ret (β := innerCtx) ⟨1, rfl⟩))
    (.ret payload)

/-- Probe the later capture and then the earlier one. -/
private def laterFirst : CaseTree older ()
    (.case (.op Probe.probe (.bv 0)) (.case (.op Probe.probe (.bv 2)) (.inl (.bv 0)) (.inl (.bv 1)))
      (.inl (.bv 0)) : Term 2) :=
  .ask Probe.probe (.atom later)
    (.ask Probe.probe (.atom earlierIn) (.ret (β := innerCtx) ⟨0, rfl⟩) (.ret (β := innerCtx) ⟨1, rfl⟩))
    (.ret payload)

/-! ## Sentences between the graphs read back from the trees -/

private abbrev sentence {t u : Term 2} (p : CaseTree older () t) (q : CaseTree older () u) :
    RankedEquation (atomSig Unit Probe) :=
  sentenceOf (entryOf p.graph) (entryOf q.graph)

/-- Exchanging the arms is observed. -/
private theorem arms_apart : ¬ RankedValid false (sentence keep flip) := fun valid => by
  have same := (rankedValid_caseTree_iff separable keep flip).mp valid
  simp at same

/-- The atom returned under one tag is observed. -/
example : ¬ RankedValid false (sentence keep both) := fun valid => by
  have same := (rankedValid_caseTree_iff separable keep both).mp valid
  simp at same

/-- The older capture used as the request argument is observed. -/
example : ¬ RankedValid false (sentence keep other) := fun valid => by
  have same := (rankedValid_caseTree_iff separable keep other).mp valid
  simp at same

/-- The order of two requests on the two older captures is observed. -/
example : ¬ RankedValid false (sentence earlierFirst laterFirst) := fun valid => by
  have same := (rankedValid_caseTree_iff separable earlierFirst laterFirst).mp valid
  simp at same

/-- A payload used as the next request argument is told apart from an
older capture used there. -/
example : ¬ RankedValid false (sentence chain earlierFirst) := fun valid => by
  have same := (rankedValid_caseTree_iff separable chain earlierFirst).mp valid
  simp at same

/-- The ordered trace model with atoms is a supported model that rejects
the sentence with exchanged arms. -/
example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Probe))
    (atomSig Unit Probe)).Sat (atomTraceRanked Unit Probe) (sentence keep flip) := fun holds =>
  arms_apart ((rankedValid_branching_iff_atomTrace separable (entryOf keep.graph) (entryOf flip.graph)
    (branching_graph keep) (branching_graph flip)).mpr holds)

/-! ## A valid sentence between two graphs

The second graph is read back from the operand emitted by the first. Its
emitted operand is natively equal to the same case tree. -/

private def chainAgain : CheckedTable Probe older [tok] :=
  CheckedTable.ofLetCase (List.cons_ne_nil _ _) chain.graph.toLetCase.2

private theorem again_branching : Branching (emitted (P := atomSig Unit Probe) (entryOf chainAgain)) :=
  Branching.congr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) chain.graph.toLetCase.2)
    (branching_graph chain)

private theorem again_valid : RankedValid false (sentenceOf (entryOf chain.graph) (entryOf chainAgain)) :=
  (rankedValid_branching_iff separable (entryOf chain.graph) (entryOf chainAgain) (branching_graph chain)
    again_branching).mpr (CheckedTable.ofLetCase_emit false (List.cons_ne_nil _ _) chain.graph.toLetCase.2).symm

/-- The ordered trace model with atoms satisfies it. -/
example : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Unit) (Φ := Probe))
    (atomSig Unit Probe)).Sat (atomTraceRanked Unit Probe)
      (sentenceOf (entryOf chain.graph) (entryOf chainAgain)) :=
  (rankedValid_branching_iff_atomTrace separable (entryOf chain.graph) (entryOf chainAgain)
    (branching_graph chain) again_branching).mp again_valid

/-- The reduction at a request node: `keep` and `both` have the same
request, so their traces differ exactly because an arm differs at some
payload token. -/
example (ρ : Isotope.Semantics.BoundEnv (LetSeq.StraightLine.Structural.Value (α := Unit)) older) :
    LetCase.Structural.Reply.run keep.typing ρ = LetCase.Structural.Reply.run both.typing ρ ↔
      (∀ x : Nat, LetCase.Structural.Reply.run (CaseTree.ret (Φ := Probe) payload).typing (ρ.snoc (A := tok) x) =
        LetCase.Structural.Reply.run (CaseTree.ret (Φ := Probe) payload).typing (ρ.snoc (A := tok) x)) ∧
      (∀ y : Nat, LetCase.Structural.Reply.run (CaseTree.ret (Φ := Probe) earlierIn).typing (ρ.snoc (A := tok) y) =
        LetCase.Structural.Reply.run (CaseTree.ret (Φ := Probe) payload).typing (ρ.snoc (A := tok) y)) :=
  ask_run_eq_iff Probe.probe (.atom earlier) (.ret payload) (.ret earlierIn) (.ret payload) (.ret payload) ρ

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

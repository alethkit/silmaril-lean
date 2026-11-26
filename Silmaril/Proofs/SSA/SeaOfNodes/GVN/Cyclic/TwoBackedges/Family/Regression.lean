module

import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Regression

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort dataPorts)
open GVN.Cyclic.TwoBackedges (WordSlot)
open GVN.Cyclic.TwoBackedges.Family
open Pure.SubZero (BinaryOpcode word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads (Quad)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Program)
open Silmaril.SSA.RVSDG (Port)

private abbrev regs : List (ValueSort Unit) :=
  [.predicate, .predicate, word, word, word, word, word, word, word, word]

private def again : Port (dataPorts regs) (.value .predicate) := .head
private def select : Port (dataPorts regs) (.value .predicate) := .tail .head
private def x : WordSlot regs := .tail (.tail .head)
private def y : WordSlot regs := .tail (.tail (.tail .head))
private def a : WordSlot regs := .tail (.tail (.tail (.tail .head)))
private def aTwin : WordSlot regs := .tail (.tail (.tail (.tail (.tail .head))))
private def b : WordSlot regs := .tail (.tail (.tail (.tail (.tail (.tail .head)))))
private def bTwin : WordSlot regs := .tail (.tail (.tail (.tail (.tail (.tail (.tail .head))))))
private def resultA : WordSlot regs :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head)))))))
private def resultTwin : WordSlot regs :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head))))))))

private def pairA : Equation regs := ⟨a, aTwin⟩
private def pairB : Equation regs := ⟨b, bTwin⟩
private def family : Equations regs := [pairA, pairB]

private def binary (op : BinaryOpcode) (dest lhs rhs : WordSlot regs) : Quad Opcode regs :=
  ⟨[word, word], word, dest, .arithmetic op, .cons lhs (.cons rhs .nil)⟩

private def stop : Quad Opcode regs := ⟨[], .predicate, again, .boolean false, .nil⟩

/-- The next A pair uses the old B pair. The next B pair uses results
derived from the old A pair before either feedback block rereads it. -/
private def fixture (reverseFalse : Bool) : Program Opcode regs word where
  preheader := [binary .add a x y, binary .add aTwin x y, binary .sub b x y, binary .sub bTwin x y]
  header := [binary .add resultA a x, binary .add resultTwin aTwin x]
  again := again
  select := select
  result := resultA
  feedback
    | true => [binary .add a b x, binary .add aTwin bTwin x,
        binary .add b resultA y, binary .add bTwin resultTwin y, stop]
    | false => [binary .sub a b x,
        if reverseFalse then binary .sub aTwin x bTwin else binary .sub aTwin bTwin x,
        binary .sub b resultA y, binary .sub bTwin resultTwin y, stop]

private def input (side : Bool) : Bank (regs := regs) model :=
  .cons ⟨true⟩ (.cons ⟨side⟩ (.cons 4#64 (.cons 1#64
    (.cons 0#64 (.cons 1#64 (.cons 2#64 (.cons 3#64 (.cons 4#64 (.cons 5#64 .nil)))))))))

private def target : Program Opcode regs word := { fixture false with result := resultTwin }

theorem overlapping_nominations_merge_their_whole_classes :
    let keys := seed ([⟨b, aTwin⟩, ⟨a, aTwin⟩] : Equations regs)
    keys.get b = keys.get a ∧ keys.get aTwin = keys.get a ∧ keys.get bTwin = .argument bTwin :=
  ⟨rfl, rfl, rfl⟩

theorem each_pair_needs_the_other_for_feedback :
    entryMatches (fixture false) family = true ∧
      feedbackMatches (fixture false) [pairA] true = false ∧
      feedbackMatches (fixture false) [pairB] true = false ∧
      feedbackMatches (fixture false) family true = true ∧
      feedbackMatches (fixture false) family false = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem simultaneous_certificate_rewrites_the_return :
    (certify? (fixture false) family resultTwin).isSome = true ∧
      rewrite? (fixture false) family resultTwin = some target ∧
      target.result = resultTwin ∧ (fixture false).result = resultA :=
  ⟨rfl, rfl, rfl, rfl⟩

private def firstFeedback (p : Program Opcode regs word) (entry : Bank (regs := regs) model) :
    Option (Bool × (BitVec 64 × BitVec 64) × (BitVec 64 × BitVec 64)) :=
  match p.step model (p.preheader.eval model entry) with
  | .inl _ => none
  | .inr (side, packet) => some (side, (packet.get a, packet.get aTwin), (packet.get b, packet.get bTwin))

theorem both_feedback_occurrences_establish_the_family :
    firstFeedback (fixture false) (input true) = some (true, (7, 7), (10, 10)) ∧
      firstFeedback (fixture false) (input false) = some (false, (-1, -1), (8, 8)) :=
  ⟨rfl, rfl⟩

theorem both_programs_return_after_the_actual_feedback :
    (fixture false).source.runFrom model 4 0 (input true) = none ∧
      (fixture false).source.runFrom model 5 0 (input true) = some 11#64 ∧
      target.source.runFrom model 5 0 (input true) = some 11#64 ∧
      (fixture false).source.runFrom model 5 0 (input false) = some 3#64 ∧
      target.source.runFrom model 5 0 (input false) = some 3#64 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem one_wrong_order_on_the_false_occurrence_refuses_the_family :
    entryMatches (fixture true) family = true ∧ feedbackMatches (fixture true) family true = true ∧
      feedbackMatches (fixture true) family false = false ∧
      feedbackFrom (fixture true) [pairB] (headerKeys (fixture true) family) false = true ∧
      exitMatches (fixture true) family resultTwin = true ∧
      (certify? (fixture true) family resultTwin).isSome = false ∧
      rewrite? (fixture true) family resultTwin = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem forcing_the_rejected_edit_changes_the_false_route_return :
    let invalid := { fixture true with result := resultTwin }
    (fixture true).source.runFrom model 5 0 (input false) = some 3#64 ∧
      invalid.source.runFrom model 5 0 (input false) = some 5#64 :=
  ⟨rfl, rfl⟩

section Discovery

open scoped GVN.Cyclic.TwoBackedges.Family.Discovery

private def laneA : Discovery.Lane regs := ⟨2, by decide⟩
private def laneATwin : Discovery.Lane regs := ⟨3, by decide⟩
private def laneB : Discovery.Lane regs := ⟨4, by decide⟩
private def laneBTwin : Discovery.Lane regs := ⟨5, by decide⟩

theorem discovery_recovers_the_mutual_family :
    Discovery.discover (fixture false) = family ∧
      (Discovery.certify? (fixture false) resultTwin).isSome = true ∧
      Discovery.rewrite? (fixture false) resultTwin = some target :=
  ⟨rfl, rfl, rfl⟩

theorem reversal_disagrees_on_only_the_false_key_of_the_first_pair :
    let p := fixture true
    let entry := Discovery.initial p
    let left := Discovery.feedbackKeys p entry laneA
    let right := Discovery.feedbackKeys p entry laneATwin
    entry laneA = entry laneATwin ∧ left.1 = right.1 ∧ left.2 ≠ right.2 ∧
      Discovery.feedbackKeys p entry laneB = Discovery.feedbackKeys p entry laneBTwin :=
  ⟨rfl, rfl, by decide, rfl⟩

theorem dependent_pair_splits_on_the_second_round :
    let p := fixture true
    let entry := Discovery.initial p
    let first := Discovery.refine p entry
    let second := Discovery.refine p first
    first laneA ≠ first laneATwin ∧ first laneB = first laneBTwin ∧
      Discovery.checkStable p first = false ∧ second laneB ≠ second laneBTwin ∧
      Discovery.checkStable p second = true ∧ Discovery.normalize p = second :=
  ⟨by decide, rfl, rfl, by decide, rfl, rfl⟩

theorem discovery_refuses_the_wrong_return_after_propagation :
    Discovery.discover (fixture true) = [] ∧
      (Discovery.certify? (fixture true) resultA).isSome = true ∧
      (Discovery.certify? (fixture true) resultTwin).isSome = false ∧
      Discovery.rewrite? (fixture true) resultTwin = none :=
  ⟨rfl, rfl, rfl, rfl⟩

open GVN.Cyclic.FixedPoint (Refines)

/-- An independently labelled discrete partition, with the labels in reverse order. -/
private def distinctClasses : Discovery.Classes regs := ⟨Vector.ofFn Fin.rev⟩

private theorem distinctClasses_label (i : Discovery.Lane regs) : distinctClasses i = i.rev := by
  change (Vector.ofFn Fin.rev).get i = i.rev
  cases i
  simp [Vector.get, Fin.cast]

private theorem distinctClasses_entry : Refines distinctClasses (Discovery.initial (fixture false)) := by
  intro i j same
  rw [distinctClasses_label, distinctClasses_label, Fin.rev_inj] at same
  rw [same]

private theorem distinctClasses_checked : Discovery.checkStable (fixture false) distinctClasses = true := rfl

theorem finer_checked_partition_refines_every_round (fuel : Nat) :
    Refines distinctClasses (Discovery.run (fixture false) fuel (Discovery.initial (fixture false))) :=
  Discovery.stable_refines_run (fixture false)
    ((Discovery.checkStable_eq_true_iff (fixture false) _).mp distinctClasses_checked) fuel _ distinctClasses_entry

theorem discovered_classes_are_strictly_coarser_than_the_finer_partition :
    Refines distinctClasses (Discovery.normalize (fixture false)) ∧
      ¬ Refines (Discovery.normalize (fixture false)) distinctClasses := by
  refine ⟨Discovery.normalize_coarsest (fixture false)
    ((Discovery.checkStable_eq_true_iff (fixture false) _).mp distinctClasses_checked) distinctClasses_entry, ?_⟩
  intro reverse
  have different : distinctClasses laneA ≠ distinctClasses laneATwin := by decide
  exact different (reverse laneA laneATwin rfl)

theorem representative_substitution_recovers_both_feedback_keys :
    let p := fixture false
    let coarse := Discovery.normalize p
    let rename := GVN.WordNumber.Key.substitute (fun port => (seed (Discovery.equations coarse)).get port)
    Discovery.feedbackKeys p distinctClasses laneA ≠ Discovery.feedbackKeys p distinctClasses laneATwin ∧
      Prod.map rename rename (Discovery.feedbackKeys p distinctClasses laneA) =
        Discovery.feedbackKeys p coarse laneATwin := by
  refine ⟨by decide, ?_⟩
  exact (Discovery.feedbackKeys_coarsen (fixture false)
    discovered_classes_are_strictly_coarser_than_the_finer_partition.1 laneA).trans rfl

end Discovery

section AutomaticReturn

private def carriedFixture (reverseFalse : Bool) : Program Opcode regs word :=
  { fixture reverseFalse with result := aTwin }

theorem automatically_redirects_the_actual_carried_return :
    Discovery.Return.returnedLane? (carriedFixture false) = some laneATwin ∧
      Discovery.Return.representative? (carriedFixture false) = some a ∧
      Discovery.Return.optimize (carriedFixture false) = { carriedFixture false with result := a } :=
  ⟨rfl, rfl, rfl⟩

theorem automatically_emitted_program_keeps_both_full_feedback_packets :
    let p := carriedFixture false
    let out := Discovery.Return.optimize p
    let onTrue := p.preheader.eval model (input true)
    let onFalse := p.preheader.eval model (input false)
    (∃ packet, p.step model onTrue = .inr (true, packet) ∧ out.step model onTrue = .inr (true, packet)) ∧
      (∃ packet, p.step model onFalse = .inr (false, packet) ∧ out.step model onFalse = .inr (false, packet)) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

theorem automatically_emitted_program_returns_on_both_routes :
    let p := carriedFixture false
    let out := Discovery.Return.optimize p
    out.source.runFrom model 4 0 (input true) = none ∧
      p.source.runFrom model 5 0 (input true) = some 7#64 ∧ out.source.runFrom model 5 0 (input true) = some 7#64 ∧
      p.source.runFrom model 5 0 (input false) = some (-1 : BitVec 64) ∧
      out.source.runFrom model 5 0 (input false) = some (-1 : BitVec 64) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem keeps_canonical_singleton_and_header_produced_returns :
    let canonical := { carriedFixture false with result := a }
    let singleton := carriedFixture true
    Discovery.Return.representative? canonical = some a ∧ Discovery.Return.optimize canonical = canonical ∧
      Discovery.Return.representative? singleton = some aTwin ∧ Discovery.Return.optimize singleton = singleton ∧
      (Discovery.Return.optimize singleton).source.runFrom model 5 0 (input false) = some 1#64 ∧
      Discovery.Return.returnedLane? (fixture false) = none ∧
      Discovery.Return.optimize (fixture false) = fixture false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def clobberedRepresentative : Program Opcode regs word :=
  { carriedFixture false with
    header := (carriedFixture false).header ++ [⟨[], word, a, .arithmetic (.literal 99#64), .nil⟩] }

theorem a_same_class_slot_with_a_different_exit_key_is_ineligible :
    Discovery.normalize clobberedRepresentative laneA = Discovery.normalize clobberedRepresentative laneATwin ∧
      exitMatches clobberedRepresentative (Discovery.discover clobberedRepresentative) a = false ∧
      Discovery.Return.representative? clobberedRepresentative = some aTwin ∧
      Discovery.Return.optimize clobberedRepresentative = clobberedRepresentative :=
  ⟨rfl, rfl, rfl, rfl⟩

end AutomaticReturn

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Regression

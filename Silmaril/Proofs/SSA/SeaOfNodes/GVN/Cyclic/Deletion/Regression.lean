module

import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN (Producer)
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation (View Site)
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint (normalize)
open Diamond (Model Signature Ty Val ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev word : ValueSort Unit := .data ()
private abbrev wordPort : Ty Unit := .value word
private abbrev guardPort : Ty Unit := .value .predicate

private inductive Primitive : Signature Unit where
  | inc : Primitive [word] word
  | test : Primitive [word] .predicate
  | observe : Primitive [.predicate, word] word

local instance : DecidableEq (ValueSort Unit) := fun a b =>
  match a, b with
  | .predicate, .predicate | .data (), .data () => isTrue rfl
  | .predicate, .data _ | .data _, .predicate => isFalse (fun h => by cases h)

local instance (ins : List (ValueSort Unit)) (out : ValueSort Unit) :
    DecidableEq (Primitive ins out) := fun a b => by
  cases a <;> cases b <;> exact isTrue rfl

private def lessThanThree (n : Nat) : Bool := decide (n < 3)

private def model : Model Primitive where
  value _ := Nat
  run
    | .inc, .cons n .nil => Nat.succ n
    | .test, .cons n .nil => ⟨lessThanThree n⟩
    | .observe, .cons p (.cons n .nil) => if p.down then n else Nat.succ n

private abbrev inputs := [word]
private abbrev carried := [word, word]
private abbrev sigs : List (List (Ty Unit)) := [[wordPort], [wordPort], [guardPort], [wordPort]]

/-- The default fixture uses producer 1 only as the guard operand.
The alternate feedback column keeps both equivalent increments live. -/
private def makeLoop (keep : Bool) : Loop.Graph Primitive inputs carried [] sigs word where
  preheader := .nil
  header := .cons .inc (.cons (.arg (.tail .head)) .nil)
    (.cons .inc (.cons (.arg (.tail (.tail .head))) .nil)
      (.cons .test (.cons (.output (1 : Fin 2) .head) .nil)
        (.cons .observe (.cons (.output (2 : Fin 3) .head) (.cons (.output (0 : Fin 3) .head) .nil)) .nil)))
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg .head) .nil)
    | .backedge =>
      if keep then
        .cons (.output (0 : Fin 4) .head) (.cons (.output (1 : Fin 4) .head) .nil)
      else
        .cons (.output (3 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil)
  predicate := .output (2 : Fin 4) .head
  result := .output (3 : Fin 4) .head

private abbrev loop := makeLoop false

private abbrev sortAt : Nat → ValueSort Unit
  | 4 => .predicate
  | _ => word

private abbrev sorts (i : Fin 6) := sortAt i.val

private def siteAt (keep : Bool) : (i : Nat) → Site (makeLoop keep) sorts (sortAt i)
  | 0 => .phi .head (if keep then .producer 2 rfl else .producer 5 rfl) .head
  | 1 => .phi .head (if keep then .producer 3 rfl else .producer 5 rfl) (.tail .head)
  | 2 => .pure .inc (.cons (.producer 0 rfl) .nil) .here
  | 3 => .pure .inc (.cons (.producer 1 rfl) .nil) (.later .here)
  | 4 => .pure .test (.cons (.producer 3 rfl) .nil) (.later (.later .here))
  | _ + 5 => .pure .observe (.cons (.producer 4 rfl) (.cons (.producer 2 rfl) .nil))
    (.later (.later (.later .here)))

private def sites (keep : Bool) (i : Fin 6) : Site (makeLoop keep) sorts (sorts i) := siteAt keep i.val

private theorem vertex_cases (i : Fin 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  simp only [Fin.ext_iff]
  omega

private def makeGraph (keep : Bool) : Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Graph Primitive inputs sorts where
  node i := (sites keep i).node
  ordered i j sort pureNode operand := by
    rcases vertex_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sites, siteAt, Site.node, Node.isPure, Node.addresses, Source.addresses, Source.address,
      Address.producer.injEq] at pureNode operand
    all_goals first
      | rcases operand with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
      | obtain ⟨_, rfl⟩ := operand
        decide

private def makeView (keep : Bool) : View (makeGraph keep) (makeLoop keep) where
  site := sites keep
  shape _ := rfl
  valid i := by
    cases keep <;> rcases vertex_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact ⟨rfl, rfl⟩ | rfl
  guard := .producer 4 rfl
  result := .producer 5 rfl
  guard_eq := rfl
  result_eq := rfl

private abbrev graph := makeGraph false
private abbrev view := makeView false

private def candidate : Producer loop.header word := .later .here
private def consumer : Producer loop.header .predicate := .later (.later .here)

theorem rejects_a_surviving_header_use : delete? loop candidate = none := rfl

private def redirected := { loop with header := HeaderUse.replaceAt consumer .head (.output (0 : Fin 2) .head) }

private theorem redirectAccepted :
    HeaderUse.redirect? view (normalize graph) consumer .head
      (.producer 3 rfl) (.producer 2 rfl) (.output (0 : Fin 2) .head) = some redirected := rfl

private def redirectedCandidate : Producer redirected.header word := .later .here

private def shortened : DeletedLoop Primitive inputs carried [] word :=
  ⟨[[wordPort], [guardPort], [wordPort]], {
    preheader := .nil
    header := .cons .inc (.cons (.arg (.tail .head)) .nil)
      (.cons .test (.cons (.output (0 : Fin 1) .head) .nil)
        (.cons .observe (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)) .nil))
    phiInputs
      | .entry => .cons (.arg .head) (.cons (.arg .head) .nil)
      | .backedge => .cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil)
    predicate := .output (1 : Fin 3) .head
    result := .output (2 : Fin 3) .head }⟩

private theorem deleteAccepted : delete? redirected redirectedCandidate = some shortened := rfl

theorem deletes_one_binding_and_updates_addresses :
    shortened.headerSigs.length = 3 ∧
      shortened.graph.predicate.producer = some 1 ∧ shortened.graph.result.producer = some 2 ∧
      (shortened.graph.phiInputs .backedge).addresses = [.output 2 0, .output 2 0] :=
  ⟨Nat.succ.inj (delete_count deleteAccepted), rfl, rfl, rfl⟩

private def input : Tuple (Val model.value) (dataPorts inputs) := .cons (0 : Nat) .nil

theorem redirect_then_delete_preserves_execution (budget : Nat) :
    shortened.graph.evalBackedges model budget input = loop.evalBackedges model budget input :=
  (delete_evalBackedges deleteAccepted model input budget).trans
    (HeaderUse.redirect_evalBackedges view consumer .head (.producer 3 rfl) (.producer 2 rfl)
      (.output (0 : Fin 2) .head) redirectAccepted model input budget)

theorem redirect_then_delete_preserves_finite_returns (value : Nat) :
    shortened.graph.Returns model input value ↔ loop.Returns model input value :=
  (delete_returns deleteAccepted model input value).trans
    (HeaderUse.redirect_returns view consumer .head (.producer 3 rfl) (.producer 2 rfl)
      (.output (0 : Fin 2) .head) redirectAccepted model input value)

theorem pipeline_returns_after_two_backedges :
    shortened.graph.evalBackedges model 1 input = none ∧
      shortened.graph.evalBackedges model 2 input = some (4 : Nat) :=
  ⟨(redirect_then_delete_preserves_execution 1).trans rfl,
    (redirect_then_delete_preserves_execution 2).trans rfl⟩

private def feedbackOnly := { redirected with
  phiInputs := fun edge => match edge with
    | .entry => redirected.phiInputs .entry
    | .backedge => .cons (.output (3 : Fin 4) .head) (.cons (.output (1 : Fin 4) .head) .nil) }

private def exitOnly := { redirected with result := .output (1 : Fin 4) .head }

theorem rejects_use_at_second_feedback_position :
    delete? feedbackOnly redirectedCandidate = none := rfl

theorem rejects_exit_only_use : delete? exitOnly redirectedCandidate = none := rfl

private def guardOnly : Loop.Graph Primitive inputs carried [] [[guardPort]] word where
  preheader := .nil
  header := .cons .test (.cons (.arg .head) .nil) .nil
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg .head) .nil)
    | .backedge => .cons (.arg .head) (.cons (.arg .head) .nil)
  predicate := .output (0 : Fin 1) .head
  result := .arg .head

theorem rejects_guard_only_use : delete? guardOnly .here = none := rfl

theorem discovers_existing_redirect_then_delete : Pass.step? view = some shortened := rfl

theorem discovered_step_shrinks_and_returns :
    shortened.headerSigs.length + 1 = sigs.length ∧
      shortened.graph.evalBackedges model 2 input = some (4 : Nat) :=
  ⟨Pass.step_count view discovers_existing_redirect_then_delete,
    (Pass.step_evalBackedges view discovers_existing_redirect_then_delete model input 2).trans rfl⟩

theorem executable_search_rejects_feedback_live_redirect :
    (HeaderUse.redirect? (makeView true) (normalize (makeGraph true)) consumer .head
      (.producer 3 rfl) (.producer 2 rfl) (.output (0 : Fin 2) .head)).isSome = true ∧
      Pass.step? (makeView true) = none :=
  ⟨rfl, rfl⟩

theorem automatically_builds_and_optimizes_the_native_loop :
    Builder.optimize? loop = some shortened := rfl

theorem native_optimization_preserves_the_result :
    shortened.graph.evalBackedges model 2 input = some (4 : Nat) :=
  (Builder.optimize_evalBackedges automatically_builds_and_optimizes_the_native_loop input 2).trans rfl

theorem rebuilds_exact_incidence_after_reindexing :
    (Builder.build? shortened.graph).map (fun built =>
      ((List.finRange (Builder.locations shortened.graph).length).map
        (fun i => (built.graph.node i).addresses), built.view.guard.address, built.view.result.address)) =
      some ([
        [.argument word 0, .producer word (4 : Fin 5)],
        [.argument word 0, .producer word (4 : Fin 5)],
        [.producer word (0 : Fin 5)],
        [.producer word (2 : Fin 5)],
        [.producer .predicate (3 : Fin 5), .producer word (2 : Fin 5)]],
        .producer .predicate (3 : Fin 5), .producer word (4 : Fin 5)) := rfl

theorem rebuilt_view_has_no_further_shrinking_step :
    (Builder.build? shortened.graph).isSome = true ∧ Builder.optimize? shortened.graph = none :=
  ⟨rfl, rfl⟩

private def crossedPhiColumns : Loop.Graph Primitive [word, word, .predicate] carried [] [] word where
  preheader := .nil
  header := .nil
  phiInputs
    | .entry => .cons (.arg (.tail .head)) (.cons (.arg .head) .nil)
    | .backedge => .cons (.arg (.tail (.tail (.tail (.tail .head)))))
        (.cons (.arg (.tail (.tail (.tail .head)))) .nil)
  predicate := .arg (.tail (.tail .head))
  result := .arg (.tail (.tail (.tail .head)))

theorem preserves_entry_and_feedback_row_order :
    (Builder.build? crossedPhiColumns).map (fun built =>
      (List.finRange (Builder.locations crossedPhiColumns).length).map
        (fun i => (built.graph.node i).addresses)) =
      some [[.argument word 1, .producer word (1 : Fin 2)],
        [.argument word 0, .producer word (0 : Fin 2)]] := rfl

private def preheaderEntry : Loop.Graph Primitive inputs carried [[wordPort]] sigs word where
  preheader := .cons .inc (.cons (.arg .head) .nil) .nil
  header := loop.header
  phiInputs
    | .entry => .cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil)
    | .backedge => loop.phiInputs .backedge
  predicate := loop.predicate
  result := loop.result

theorem rejects_phi_entry_from_a_preheader_producer : Builder.build? preheaderEntry = none := rfl

private abbrev twoDuplicateSigs : List (List (Ty Unit)) :=
  [[wordPort], [wordPort], [wordPort], [guardPort], [wordPort]]

/-- Each duplicate increment has one use. The first feeds the guard and
the second feeds the exit computation. The original increment feeds both
feedback positions, keeping it live throughout the two rewrites. -/
private def twoDuplicates : Loop.Graph Primitive inputs carried [] twoDuplicateSigs word where
  preheader := .nil
  header := .cons .inc (.cons (.arg (.tail .head)) .nil)
    (.cons .inc (.cons (.arg (.tail (.tail .head))) .nil)
      (.cons .inc (.cons (.arg (.tail (.tail .head))) .nil)
        (.cons .test (.cons (.output (1 : Fin 3) .head) .nil)
          (.cons .observe (.cons (.output (3 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil))
            .nil))))
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg .head) .nil)
    | .backedge => .cons (.output (0 : Fin 5) .head) (.cons (.output (0 : Fin 5) .head) .nil)
  predicate := .output (3 : Fin 5) .head
  result := .output (4 : Fin 5) .head

private def afterFirst : DeletedLoop Primitive inputs carried [] word :=
  ⟨sigs, {
    preheader := .nil
    header := .cons .inc (.cons (.arg (.tail .head)) .nil)
      (.cons .inc (.cons (.arg (.tail (.tail .head))) .nil)
        (.cons .test (.cons (.output (0 : Fin 2) .head) .nil)
          (.cons .observe (.cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil))
            .nil)))
    phiInputs
      | .entry => .cons (.arg .head) (.cons (.arg .head) .nil)
      | .backedge => .cons (.output (0 : Fin 4) .head) (.cons (.output (0 : Fin 4) .head) .nil)
    predicate := .output (2 : Fin 4) .head
    result := .output (3 : Fin 4) .head }⟩

private def afterSecond : DeletedLoop Primitive inputs carried [] word :=
  { shortened with graph := { shortened.graph with phiInputs := fun edge => match edge with
    | .entry => shortened.graph.phiInputs .entry
    | .backedge => .cons (.output (0 : Fin 3) .head) (.cons (.output (0 : Fin 3) .head) .nil) } }

private theorem firstDeletion : Builder.optimize? twoDuplicates = some afterFirst := rfl
private theorem secondDeletion : Builder.optimize? afterFirst.graph = some afterSecond := rfl
private theorem finalStep : Builder.optimize? afterSecond.graph = none := rfl

private def repeated := Iteration.normalize twoDuplicates

private theorem repeatedResult : repeated = ⟨afterSecond, 2⟩ := by
  change Iteration.run 5 twoDuplicates = _
  simp only [Iteration.run, firstDeletion, secondDeletion, finalStep]

theorem two_fresh_steps_remove_two_bindings :
    (Builder.optimize? twoDuplicates).map (·.headerSigs.length) = some 4 ∧
      ((Builder.optimize? twoDuplicates).bind
        (fun first => (Builder.optimize? first.graph).map (·.headerSigs.length))) = some 3 ∧
      repeated.deletions = 2 ∧ repeated.rewrite.headerSigs.length = 3 := by
  rw [firstDeletion, Option.bind_some, secondDeletion, repeatedResult]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem repeated_search_remains_buildable_and_stops :
    (Builder.build? repeated.rewrite.graph).isSome = true ∧
      Builder.optimize? repeated.rewrite.graph = none := by
  rw [repeatedResult]
  exact ⟨rfl, finalStep⟩

theorem repeated_rewrite_preserves_observations :
    repeated.rewrite.graph.evalBackedges model 1 input = none ∧
      repeated.rewrite.graph.evalBackedges model 2 input = some (4 : Nat) ∧
      (repeated.rewrite.graph.Returns model input (4 : Nat) ↔ twoDuplicates.Returns model input (4 : Nat)) :=
  ⟨(Iteration.normalize_evalBackedges (m := model) twoDuplicates input 1).trans rfl,
    (Iteration.normalize_evalBackedges (m := model) twoDuplicates input 2).trans rfl,
    Iteration.normalize_returns (m := model) twoDuplicates input (4 : Nat)⟩

theorem iteration_stops_on_outside_profile :
    (Iteration.normalize preheaderEntry).deletions = 0 ∧
      (Iteration.normalize preheaderEntry).rewrite = ⟨sigs, preheaderEntry⟩ :=
  ⟨rfl, rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression

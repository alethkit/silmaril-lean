module

import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Thms
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

/-- Producer 1's only use is the guard operand. The output reads both
producer 0 and the guard, so deleting 1 also shifts a surviving operand. -/
private def loop : Loop.Graph Primitive inputs carried [] sigs word where
  preheader := .nil
  header := .cons .inc (.cons (.arg (.tail .head)) .nil)
    (.cons .inc (.cons (.arg (.tail (.tail .head))) .nil)
      (.cons .test (.cons (.output (1 : Fin 2) .head) .nil)
        (.cons .observe (.cons (.output (2 : Fin 3) .head) (.cons (.output (0 : Fin 3) .head) .nil)) .nil)))
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg .head) .nil)
    | .backedge => .cons (.output (3 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil)
  predicate := .output (2 : Fin 4) .head
  result := .output (3 : Fin 4) .head

private abbrev sortAt : Nat → ValueSort Unit
  | 4 => .predicate
  | _ => word

private abbrev sorts (i : Fin 6) := sortAt i.val

private def siteAt : (i : Nat) → Site loop sorts (sortAt i)
  | 0 => .phi .head (.producer 5 rfl) .head
  | 1 => .phi .head (.producer 5 rfl) (.tail .head)
  | 2 => .pure .inc (.cons (.producer 0 rfl) .nil) .here
  | 3 => .pure .inc (.cons (.producer 1 rfl) .nil) (.later .here)
  | 4 => .pure .test (.cons (.producer 3 rfl) .nil) (.later (.later .here))
  | _ + 5 => .pure .observe (.cons (.producer 4 rfl) (.cons (.producer 2 rfl) .nil))
    (.later (.later (.later .here)))

private def sites (i : Fin 6) : Site loop sorts (sorts i) := siteAt i.val

private theorem vertex_cases (i : Fin 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
  simp only [Fin.ext_iff]
  omega

private def graph : Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Graph Primitive inputs sorts where
  node i := (sites i).node
  ordered i j sort pureNode operand := by
    rcases vertex_cases i with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [sites, siteAt, Site.node, Node.isPure, Node.addresses, Source.addresses, Source.address,
      Address.producer.injEq] at pureNode operand
    all_goals first
      | rcases operand with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
      | obtain ⟨_, rfl⟩ := operand
        decide

private def view : View graph loop where
  site := sites
  shape _ := rfl
  valid i := by
    rcases vertex_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact ⟨rfl, rfl⟩ | rfl
  guard := .producer 4 rfl
  result := .producer 5 rfl
  guard_eq := rfl
  result_eq := rfl

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

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression

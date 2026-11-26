module

import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint (normalize normalize_stable)
open Diamond (Model Signature Ty ValueSort)
open Silmaril.SSA.RVSDG (Origin Tuple)

private abbrev word : ValueSort Unit := .data ()
private abbrev wordPort : Ty Unit := .value word
private abbrev guardPort : Ty Unit := .value .predicate

private inductive Primitive : Signature Unit where
  | inc : Primitive [word] word
  | belowThree : Primitive [word] .predicate

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
    | .belowThree, .cons n .nil => ⟨lessThanThree n⟩

private abbrev inputs := [word]
private abbrev carried := [word, word]

/-- Both latches start at the input and increment on each backedge. The
guard consumes the first increment before the second increment is bound. -/
private def loop : Loop.Graph Primitive inputs carried [] [[wordPort], [guardPort], [wordPort]] word where
  preheader := .nil
  header := .cons .inc (.cons (.arg (.tail .head)) .nil)
    (.cons .belowThree (.cons (.output (0 : Fin 1) .head) .nil)
      (.cons .inc (.cons (.arg (.tail (.tail .head))) .nil) .nil))
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg .head) .nil)
    | .backedge => .cons (.output (0 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil)
  predicate := .output (1 : Fin 3) .head
  result := .output (0 : Fin 3) .head

private abbrev sortAt : Nat → ValueSort Unit
  | 3 => .predicate
  | _ => word

private abbrev sorts (i : Fin 5) := sortAt i.val

private def siteAt : (i : Nat) → Site loop sorts (sortAt i)
  | 0 => .phi .head (.producer 2 rfl) .head
  | 1 => .phi .head (.producer 4 rfl) (.tail .head)
  | 2 => .pure .inc (.cons (.producer 0 rfl) .nil) .here
  | 3 => .pure .belowThree (.cons (.producer 2 rfl) .nil) (.later .here)
  | _ + 4 => .pure .inc (.cons (.producer 1 rfl) .nil) (.later (.later .here))

private def sites (i : Fin 5) : Site loop sorts (sorts i) := siteAt i.val

private theorem vertex_cases (i : Fin 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  simp only [Fin.ext_iff]
  omega

private def graph : Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Graph Primitive inputs sorts where
  node i := (sites i).node
  ordered i j sort pureNode operand := by
    rcases vertex_cases i with rfl | rfl | rfl | rfl | rfl
    all_goals simp [sites, siteAt, Site.node, Node.isPure, Node.addresses, Source.addresses, Source.address,
      Address.producer.injEq] at pureNode operand
    all_goals obtain ⟨_, rfl⟩ := operand
    all_goals decide

private def view : View graph loop where
  site := sites
  shape _ := rfl
  valid i := by
    rcases vertex_cases i with rfl | rfl | rfl | rfl | rfl <;> first | exact ⟨rfl, rfl⟩ | rfl
  guard := .producer 3 rfl
  result := .producer 2 rfl
  guard_eq := rfl
  result_eq := rfl

private def partition := normalize graph
private theorem stable : Stable graph partition := (normalize_stable graph).1

private def input : Inputs model inputs := .cons (0 : Nat) .nil
private def latches (n : Nat) : Inputs model carried := .cons n (.cons n .nil)

theorem class_agreement_through_two_backedges :
    view.ClassesAgree partition model input (latches 0) input (latches 0) ∧
      view.ClassesAgree partition model input (latches 1) input (latches 1) ∧
      view.ClassesAgree partition model input (latches 2) input (latches 2) := by
  have fixed : InputsAgree model input input := fun _ => rfl
  have initial : loop.initial model input = latches 0 := rfl
  have first := view.initial_agrees stable fixed
  rw [initial] at first
  have firstStep : loop.step model input (latches 0) = .inr (latches 1) := rfl
  have second := (view.step_agrees stable fixed first).2
  rw [firstStep] at second
  have secondStep : loop.step model input (latches 1) = .inr (latches 2) := rfl
  have third := (view.step_agrees stable fixed second).2
  rw [secondStep] at third
  exact ⟨view.header_agrees stable fixed first,
    view.header_agrees stable fixed second, view.header_agrees stable fixed third⟩

private def representative : Source inputs sorts word := .producer 4 rfl
private def rewritten := view.redirectResult partition representative

theorem redirects_the_exit_and_retains_its_result :
    loop.result.producer = some 0 ∧ rewritten.result.producer = some 2 ∧
      rewritten.evalBackedges model 2 input = some (3 : Nat) :=
  ⟨rfl, rfl, (view.redirect_evalBackedges partition representative model input 2).trans rfl⟩

theorem rejects_a_different_class :
    (view.redirectResult partition (.producer 0 rfl)).result = loop.result := rfl

/-- The exit representative has no address in the guard's one-binding prefix. -/
theorem representative_unavailable_at_guard :
    ¬ ∃ wire : Origin (Loop.headerPorts inputs carried) [[wordPort]] wordPort,
      wire.producer = rewritten.result.producer := by
  rintro ⟨wire, same⟩
  have index : rewritten.result.producer = some 2 := rfl
  rw [index] at same
  cases wire with
  | arg => cases same
  | output i _ =>
    have invalid : i.val = 2 := Option.some.inj same
    have bound := i.isLt
    simp only [List.length_cons, List.length_nil] at bound
    omega

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation.Regression

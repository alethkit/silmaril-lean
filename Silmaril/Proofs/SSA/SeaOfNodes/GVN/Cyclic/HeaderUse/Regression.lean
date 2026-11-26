module

import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Regression

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN (Producer)
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint (normalize normalize_stable)
open Diamond (Model Signature Ty ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Origin Port)

private abbrev word : ValueSort Unit := .data ()
private abbrev wordPort : Ty Unit := .value word
private abbrev guardPort : Ty Unit := .value .predicate

private inductive Primitive : Signature Unit where
  | inc : Primitive [word] word
  | test : Primitive [word, word] .predicate

local instance : DecidableEq (ValueSort Unit) := fun a b =>
  match a, b with
  | .predicate, .predicate | .data (), .data () => isTrue rfl
  | .predicate, .data _ | .data _, .predicate => isFalse (fun h => by cases h)

local instance (ins : List (ValueSort Unit)) (out : ValueSort Unit) :
    DecidableEq (Primitive ins out) := fun a b => by
  cases a <;> cases b <;> exact isTrue rfl

private def guardTest (left right : Nat) : Bool := (left == right) && decide (left < 3)

private def model : Model Primitive where
  value _ := Nat
  run
    | .inc, .cons n .nil => Nat.succ n
    | .test, .cons lhs (.cons rhs .nil) => ⟨guardTest lhs rhs⟩

private abbrev inputs := [word]
private abbrev carried := [word, word]
private abbrev signatures : List (List (Ty Unit)) := [[wordPort], [wordPort], [guardPort], [wordPort]]

/-- The guard at position 2 reads producer 0 twice. Producers 1 and 3
are equivalent to producer 0, but producer 3 is bound after the guard.
The first and last increments feed the two feedback slots. -/
private def loop : Loop.Graph Primitive inputs carried [] signatures word where
  preheader := .nil
  header := .cons .inc (.cons (.arg (.tail .head)) .nil)
    (.cons .inc (.cons (.arg (.tail (.tail .head))) .nil)
      (.cons .test (.cons (.output (0 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil))
        (.cons .inc (.cons (.arg (.tail (.tail .head))) .nil) .nil)))
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg .head) .nil)
    | .backedge => .cons (.output (0 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil)
  predicate := .output (2 : Fin 4) .head
  result := .output (0 : Fin 4) .head

private abbrev sortAt : Nat → ValueSort Unit
  | 4 => .predicate
  | _ => word

private abbrev sorts (i : Fin 6) := sortAt i.val

private def siteAt : (i : Nat) → Site loop sorts (sortAt i)
  | 0 => .phi .head (.producer 2 rfl) .head
  | 1 => .phi .head (.producer 5 rfl) (.tail .head)
  | 2 => .pure .inc (.cons (.producer 0 rfl) .nil) .here
  | 3 => .pure .inc (.cons (.producer 1 rfl) .nil) (.later .here)
  | 4 => .pure .test (.cons (.producer 2 rfl) (.cons (.producer 2 rfl) .nil)) (.later (.later .here))
  | _ + 5 => .pure .inc (.cons (.producer 1 rfl) .nil) (.later (.later (.later .here)))

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
    all_goals obtain ⟨_, rfl⟩ := operand
    all_goals decide

private def view : View graph loop where
  site := sites
  shape _ := rfl
  valid i := by
    rcases vertex_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact ⟨rfl, rfl⟩ | rfl
  guard := .producer 4 rfl
  result := .producer 2 rfl
  guard_eq := rfl
  result_eq := rfl

private def partition := normalize graph
private def consumer : Producer loop.header .predicate := .later (.later .here)
private def use : Port (dataPorts consumer.key.ins) wordPort := .tail .head
private def original : Source inputs sorts word := .producer 2 rfl
private def earlier : Source inputs sorts word := .producer 3 rfl
private def later : Source inputs sorts word := .producer 5 rfl

private abbrev PrefixWire :=
  Origin (Loop.headerPorts inputs carried) (GVN.Elimination.operandScope consumer) wordPort

private def earlierWire : PrefixWire := .output (1 : Fin 2) .head
private def edited := { loop with header := replaceAt consumer use earlierWire }

private theorem accepted : redirect? view partition consumer use original earlier earlierWire = some edited := rfl

private def editedConsumer : Producer edited.header .predicate := .later (.later .here)

theorem rewrites_only_the_selected_occurrence :
    (operandAt consumer use).producer = some 0 ∧
      (operandAt editedConsumer use).producer = some 1 ∧
      (operandAt editedConsumer .head).producer = some 0 :=
  ⟨rfl, rfl, rfl⟩

theorem rejects_later_equivalent_producer :
    original.address.relabel partition = later.address.relabel partition ∧
      ∀ prefixWire : PrefixWire, redirect? view partition consumer use original later prefixWire = none := by
  refine ⟨rfl, ?_⟩
  intro prefixWire
  unfold redirect?
  split
  · rename_i checked
    have actual := ((check_eq_true_iff view consumer use original later prefixWire).mp checked).2.2.2
    have address := congrArg Origin.producer actual
    cases prefixWire with
    | arg => cases address
    | output i _ =>
      change Fin 2 at i
      have range : i = 0 ∨ i = 1 := by
        have bound : i.val < 2 := i.isLt
        simp only [Fin.ext_iff]
        omega
      rcases range with rfl | rfl <;> cases address
  · rfl

theorem rejects_a_different_original_wire :
    redirect? view partition consumer use earlier original (.output (0 : Fin 2) .head) = none := rfl

private def input : Inputs model inputs := .cons (0 : Nat) .nil
private def latches (n : Nat) : Inputs model carried := .cons n (.cons n .nil)

theorem preserves_two_backedges_and_exit :
    edited.step model input (latches 0) = .inr (latches 1) ∧
      edited.step model input (latches 1) = .inr (latches 2) ∧
      edited.evalBackedges model 2 input = some (3 : Nat) := by
  have fixed : InputsAgree model input input := fun _ => rfl
  have initial : view.LatchesAgree partition model (latches 0) (latches 0) :=
    view.initial_agrees (normalize_stable graph).1 fixed
  have step₀ := (redirect_step view consumer use original earlier earlierWire accepted model input _ initial).2
  have taken₀ : edited.step model input (latches 0) = .inr (latches 1) := step₀.1.trans rfl
  have step₁ := (redirect_step view consumer use original earlier earlierWire accepted model input _
    (step₀.2 _ taken₀)).2.1
  exact ⟨taken₀, step₁.trans rfl,
    (redirect_evalBackedges view consumer use original earlier earlierWire accepted model input 2).trans rfl⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Regression

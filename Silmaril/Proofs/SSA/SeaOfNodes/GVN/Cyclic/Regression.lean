module

import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Regression

open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.Diamond (Signature ValueSort)
open Silmaril.SSA.RVSDG (Tuple)

private abbrev int : ValueSort Unit := .data ()

private inductive Arithmetic : Signature Unit where
  | sub : Arithmetic [int, int] int

local instance : DecidableEq (ValueSort Unit) := fun a b =>
  match a, b with
  | .predicate, .predicate | .data (), .data () => isTrue rfl
  | .predicate, .data _ | .data _, .predicate => isFalse (fun h => by cases h)

local instance (ins : List (ValueSort Unit)) (out : ValueSort Unit) :
    DecidableEq (Arithmetic ins out) := fun a b => by
  cases a
  cases b
  exact isTrue rfl

private abbrev sorts : Fin 7 → ValueSort Unit := fun _ => int
private abbrev inputs := [int, int, int]

private def producer (i : Fin 7) : Source inputs sorts int := .producer i rfl

private def subtract (left right : Source inputs sorts int) : Node Arithmetic inputs sorts int :=
  .pure .sub (.cons left (.cons right .nil))

/-- The loops through Phi vertices 0, 1 and 2 respectively carry
`x - a`, `y - b` and `z - a`, with a shared entry argument.
Vertex 6 reverses the operands of vertex 3. -/
private def node (i : Fin 7) : Node Arithmetic inputs sorts (sorts i) :=
  match i.val with
  | 0 => .phi .head (producer 3)
  | 1 => .phi .head (producer 4)
  | 2 => .phi .head (producer 5)
  | 3 => subtract (producer 0) (.argument (.tail .head))
  | 4 => subtract (producer 1) (.argument (.tail (.tail .head)))
  | 5 => subtract (producer 2) (.argument (.tail .head))
  | _ => subtract (.argument (.tail .head)) (producer 0)

private def fixture : Graph Arithmetic inputs sorts where
  node := node
  ordered i j sort pureNode operand := by
    have casesI : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
        i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by omega
    rcases casesI with h | h | h | h | h | h | h
    all_goals simp [node, h, Node.isPure, Node.addresses, subtract, producer,
      Source.addresses, Source.address, Address.producer.injEq] at pureNode operand
    all_goals obtain ⟨_, rfl⟩ := operand
    all_goals change _ < i.val
    all_goals simp [h]

private def initial := seed fixture
private def first := refine fixture initial
private def second := refine fixture first

theorem distinction_crosses_backedge_on_second_round :
    initial 3 = initial 4 ∧ first 3 ≠ first 4 ∧ first 0 = first 1 ∧ second 0 ≠ second 1 := by
  decide

theorem reversed_operands_split : initial 3 = initial 6 ∧ first 3 ≠ first 6 := by
  decide

theorem checker_detects_split_then_accepts :
    checkStable fixture initial = false ∧ checkStable fixture first = false ∧
    checkStable fixture second = true ∧ second 0 = second 2 ∧ second 3 = second 5 := by
  decide

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Regression

module

public import Silmaril.Semantics.RuntimeWires.SeamTrace.Defs
import Silmaril.Semantics.RuntimeWires.ProgressiveTrace.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.SeamTrace

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

theorem rename_ports (route : BoxAddress → BoxAddress) (row box : ℕ) (word : List O) :
    (namePorts (.box row box) word).map (NamedWire.rename route) =
      namePorts (.box (route (row, box)).1 (route (row, box)).2) word := by
  simp [namePorts, List.map_map, Function.comp_def, NamedWire.rename, WireOrigin.rename]

private theorem route_head {route : BoxAddress → BoxAddress} {row first : ℕ}
    {head : BoxAddress} {rest : List BoxAddress} (h : RoutesBoxes route row first (head :: rest)) :
    route (row, first) = head := by
  have atZero := h 0 (by simp)
  change route (row, first + 0) = head at atZero
  exact atZero

private theorem route_tail {route : BoxAddress → BoxAddress} {row first : ℕ}
    {head : BoxAddress} {rest : List BoxAddress} (h : RoutesBoxes route row first (head :: rest)) :
    RoutesBoxes route row (first + 1) rest := by
  intro i hi
  have eq : first + 1 + i = first + (i + 1) := by omega
  have next := h (i + 1) (by simpa using hi)
  change route (row, first + (i + 1)) = rest[i] at next
  rwa [eq]

theorem trace_split_rows {A M B : List O} {r : Row S A B} {p : Row S A M} {q : Row S M B}
    (split : Row.Split S r p q) (row upper lower : ℕ) :
    ∃ destinations : List BoxAddress, destinations.length = r.boxCount ∧
      ∀ (route : BoxAddress → BoxAddress) (first : ℕ), RoutesBoxes route row first destinations →
      ∀ input : List (NamedWire O), input.length = A.length →
        let original := r.traceWires row first input
        let sliced := traceSplitRows p q row upper lower (input.map (NamedWire.rename route))
        original.frontier.map (NamedWire.rename route) = sliced.1 ∧
          ((addressBoxes row first original.boxes).map (BoxOccurrence.rename route)).Perm sliced.2 := by
  induction split generalizing upper lower with
  | empty =>
    refine ⟨[], rfl, ?_⟩
    intro route first align input count
    exact ⟨rfl, .nil⟩
  | wire x split ih =>
    obtain ⟨destinations, size, tail⟩ := ih upper lower
    refine ⟨destinations, size, ?_⟩
    intro route first align input count
    cases input with
    | nil => simp at count
    | cons head input =>
      have ok := tail route first align input (Nat.succ.inj count)
      constructor
      · simpa [Row.traceWires, traceSplitRows] using congrArg (List.cons (NamedWire.rename route head)) ok.1
      · simpa [Row.traceWires, traceSplitRows] using ok.2
  | @upper e A M B r p q split ih =>
    obtain ⟨destinations, size, tail⟩ := ih (upper + 1) lower
    refine ⟨(row, upper) :: destinations, congrArg Nat.succ size, ?_⟩
    intro route first align input count
    let ins := input.take (S.source e).length
    let rest := input.drop (S.source e).length
    have takeCount : (ins.map (NamedWire.rename route)).length = (S.source e).length := by
      simp [ins, count]
    have dropCount : rest.length = A.length := by
      simp [rest, count]
    have ok := tail route (first + 1) (route_tail align) rest dropCount
    have names := rename_ports route row first (S.target e)
    rw [route_head align] at names
    have pass := Row.traceWires_pass q (S.target e) (namePorts (.box row upper) (S.target e))
      (p.traceWires row (upper + 1) (rest.map (NamedWire.rename route))).frontier
      (by simp [namePorts]) (row + 1) lower
    have input_eq : input = ins ++ rest := (List.take_append_drop ..).symm
    have splitInput : input.map (NamedWire.rename route) =
        ins.map (NamedWire.rename route) ++ rest.map (NamedWire.rename route) :=
      (congrArg (List.map (NamedWire.rename route)) input_eq).trans List.map_append
    simp only [Row.traceWires, traceSplitRows, splitInput, List.take_left' takeCount,
      List.drop_left' takeCount, pass, List.map_append, names,
      addressBoxes, List.map_cons, List.cons_append, BoxOccurrence.rename, BoxTrace.rename, route_head align]
    constructor
    · exact congrArg (namePorts (.box row upper) (S.target e) ++ ·) ok.1
    · exact ok.2.cons _
  | @lower e A M B r p q split ih =>
    obtain ⟨destinations, size, tail⟩ := ih upper (lower + 1)
    refine ⟨(row + 1, lower) :: destinations, congrArg Nat.succ size, ?_⟩
    intro route first align input count
    let ins := input.take (S.source e).length
    let rest := input.drop (S.source e).length
    have takeCount : (ins.map (NamedWire.rename route)).length = (S.source e).length := by
      simp [ins, count]
    have dropCount : rest.length = A.length := by
      simp [rest, count]
    have ok := tail route (first + 1) (route_tail align) rest dropCount
    have names := rename_ports route row first (S.target e)
    rw [route_head align] at names
    have pass := Row.traceWires_pass p (S.source e) (ins.map (NamedWire.rename route))
      (rest.map (NamedWire.rename route)) takeCount row upper
    have input_eq : input = ins ++ rest := (List.take_append_drop ..).symm
    have splitInput : input.map (NamedWire.rename route) =
        ins.map (NamedWire.rename route) ++ rest.map (NamedWire.rename route) :=
      (congrArg (List.map (NamedWire.rename route)) input_eq).trans List.map_append
    simp only [Row.traceWires, traceSplitRows, splitInput, pass, List.take_left' takeCount,
      List.drop_left' takeCount, List.map_append, names, addressBoxes, List.map_cons, BoxOccurrence.rename,
      BoxTrace.rename, route_head align]
    constructor
    · exact congrArg (namePorts (.box (row + 1) lower) (S.target e) ++ ·) ok.1
    · exact (ok.2.cons _).trans List.perm_middle.symm

end Silmaril.RuntimeWires.Proofs.SeamTrace

module

public import Silmaril.Semantics.RuntimeWires.ProgressiveTrace.Defs
import Mathlib.Data.List.Zip

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveTrace

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

theorem namePorts_map {I : Type*} [BEq I] [LawfulBEq I] (wires : List I) (nd : wires.Nodup)
    (label : I → O) (source : ℕ → WireOrigin) :
    namePorts source (wires.map label) =
      wires.map (fun w => (label w, source (wires.idxOf w))) := by
  apply List.ext_getElem (by simp [namePorts])
  intro i h₁ h₂
  simp only [namePorts, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  rw [nd.idxOf_getElem]

theorem trace_straight (word : List O) (input : List (NamedWire O))
    (hl : input.length = word.length) (row box : ℕ) :
    (Row.straight (S := S) word).traceWires row box input = ⟨input, []⟩ := by
  induction word generalizing input with
  | nil =>
    have he : input = [] := List.eq_nil_of_length_eq_zero hl
    subst input
    rfl
  | cons x word ih =>
    cases input with
    | nil => simp at hl
    | cons n input =>
      have he : input.length = word.length := Nat.succ.inj hl
      simp [Row.straight, Row.traceWires, ih input he]

theorem trace_pass {A B : List O} (r : Row S A B) (word : List O)
    (leftNames input : List (NamedWire O)) (hl : leftNames.length = word.length) (row box : ℕ) :
    (Row.pass word r).traceWires row box (leftNames ++ input) =
      ⟨leftNames ++ (r.traceWires row box input).frontier, (r.traceWires row box input).boxes⟩ := by
  induction word generalizing leftNames with
  | nil =>
    have he : leftNames = [] := List.eq_nil_of_length_eq_zero hl
    subst leftNames
    rfl
  | cons x word ih =>
    cases leftNames with
    | nil => simp at hl
    | cons n leftNames =>
      have he : leftNames.length = word.length := Nat.succ.inj hl
      simp [Row.pass, Row.traceWires, ih leftNames he]

theorem trace_one_box (e : S.Edge) (leftWord rightWord : List O)
    (left inputs right : List (NamedWire O)) (row : ℕ)
    (hl : left.length = leftWord.length) (hi : inputs.length = (S.source e).length)
    (hr : right.length = rightWord.length) :
    (Row.pass leftWord (.box e (Row.straight rightWord))).traceWires row 0
      (left ++ (inputs ++ right)) =
      ⟨left ++ (namePorts (.box row 0) (S.target e) ++ right),
        [⟨e, inputs, namePorts (.box row 0) (S.target e)⟩]⟩ := by
  rw [trace_pass _ _ _ _ hl]
  simp only [Row.traceWires, List.take_left' hi, List.drop_left' hi, trace_straight rightWord right hr]

theorem trace_transport {A B C D : List O} (hA : A = C) (hB : B = D) (r : Row S A B)
    (row box : ℕ) (input : List (NamedWire O)) :
    ((congrArg₂ (Row S) hA hB).mp r).traceWires row box input = r.traceWires row box input := by
  subst C
  subst D
  rfl

theorem trace_transport_symm {A B C D : List O} (hA : A = C) (hB : B = D) (r : Row S C D)
    (row box : ℕ) (input : List (NamedWire O)) :
    ((congrArg₂ (Row S) hA hB).symm.mp r).traceWires row box input = r.traceWires row box input := by
  subst C
  subst D
  rfl

end Silmaril.RuntimeWires.Proofs.ProgressiveTrace

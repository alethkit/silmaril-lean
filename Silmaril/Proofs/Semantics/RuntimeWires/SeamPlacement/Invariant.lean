module

public import Silmaril.Semantics.RuntimeWires.SeamPlacement.Defs

public section

namespace Silmaril.RuntimeWires.Proofs.SeamPlacement

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

theorem row_boundary {A B : List O} (r : Row S A B)
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) : A = B := by
  induction r with
  | empty => rfl
  | wire x r ih => exact congrArg (x :: ·) ih
  | box e r ih => simpa only [(nullary e).1, (nullary e).2, List.nil_append] using ih

private theorem pass_empty {word A B : List O} (r : Row S A B) (nil : word = []) :
    (Row.pass word r).boxesBeforeFirstWire = r.boxesBeforeFirstWire := by
  subst word
  rfl

theorem split_count {A M B : List O} {r : Row S A B} {p : Row S A M} {q : Row S M B}
    (split : Row.Split S r p q) (nullary : ∀ e, S.source e = [] ∧ S.target e = []) :
    r.boxesBeforeFirstWire = p.boxesBeforeFirstWire + q.boxesBeforeFirstWire := by
  induction split with
  | empty => rfl
  | wire => rfl
  | upper e _ ih =>
    simp only [Row.boxesBeforeFirstWire, pass_empty _ (nullary e).2, ih]
    omega
  | lower e _ ih =>
    simp only [Row.boxesBeforeFirstWire, pass_empty _ (nullary e).1, ih]
    omega

private theorem straight_count (word : List O) :
    (Row.straight (S := S) word).boxesBeforeFirstWire = 0 := by
  cases word <;> rfl

theorem move_count {A B : List O} {p q : Sheet S A B} (move : Sheet.Move S p q)
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) :
    p.boxesBeforeFirstWire = q.boxesBeforeFirstWire := by
  induction move with
  | split split tail =>
    simp only [Sheet.boxesBeforeFirstWire, split_count split nullary, Nat.add_assoc]
  | straight tail =>
    simp only [Sheet.boxesBeforeFirstWire, straight_count, Nat.zero_add]
  | under row _ ih =>
    simp only [Sheet.boxesBeforeFirstWire, ih]

theorem seam_count {A B : List O} {p q : Sheet S A B} (same : Sheet.SeamEquivalent p q)
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) :
    p.boxesBeforeFirstWire = q.boxesBeforeFirstWire := by
  induction same with
  | rel _ _ move => exact move_count move nullary
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ a b => exact a.trans b

theorem counterexample : ¬ Sheet.SeamEquivalent NullaryPlacement.scalarLeft NullaryPlacement.scalarRight := by
  intro same
  have count := seam_count same (fun _ => ⟨rfl, rfl⟩)
  change 1 = 0 at count
  exact Nat.one_ne_zero count

end Silmaril.RuntimeWires.Proofs.SeamPlacement

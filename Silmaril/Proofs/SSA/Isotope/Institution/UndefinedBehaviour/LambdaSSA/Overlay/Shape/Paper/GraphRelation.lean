module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

universe u v w x

variable {P : Type u} {Q : Type v} {O : Type w} {O' : Type x}
  {f : Graph P O} {g : Graph Q O'} {R : P → Q → Prop}

/-- Match actual steps in both directions. Related points may have different
label numbers, while a matched successor retains its payload and state. -/
structure Matches (f : Graph P O) (g : Graph Q O') (R : P → Q → Prop) : Prop where
  forward : ∀ {a b c}, R a b → f.step a c → ∃ d, g.step b d ∧ R c d
  backward : ∀ {a b d}, R a b → g.step b d → ∃ c, f.step a c ∧ R c d

namespace Matches

theorem symm (m : Matches f g R) : Matches g f (fun b a => R a b) :=
  ⟨m.backward, m.forward⟩

private theorem finite_forward (m : Matches f g R) {a : P} {b : Q} {o : O} {o' : O'}
    (terminal : ∀ {p q}, R p q → f.finish p o → g.finish q o')
    (run : f.Finite a o) (related : R a b) :
    g.Finite b o' := by
  obtain ⟨c, reach, finish⟩ := run
  induction reach using Relation.ReflTransGen.head_induction_on generalizing b with
  | refl => exact ⟨b, .refl, terminal related finish⟩
  | head step _ ih =>
    obtain ⟨d, edge, related⟩ := m.forward related step
    obtain ⟨q, reach, finish⟩ := ih related
    exact ⟨q, reach.head edge, finish⟩

theorem finite_iff (m : Matches f g R) {a : P} {b : Q} {o : O} {o' : O'}
    (terminal : ∀ {p q}, R p q → (f.finish p o ↔ g.finish q o'))
    (related : R a b) : f.Finite a o ↔ g.Finite b o' :=
  ⟨fun run => m.finite_forward (fun r => (terminal r).mp) run related,
    fun run => m.symm.finite_forward (fun r => (terminal r).mpr) run related⟩

private theorem infinite_forward (m : Matches f g R) {a : P} {b : Q}
    (run : f.Infinite a) (related : R a b) : g.Infinite b := by
  obtain ⟨path, start, step⟩ := run
  let Lift (n : Nat) := {q // R (path n) q}
  have next (n : Nat) (q : Lift n) : ∃ t, g.step q.val t ∧ R (path (n + 1)) t :=
    m.forward q.property (step n)
  let lifted : (n : Nat) → Lift n := Nat.rec ⟨b, start.symm ▸ related⟩
    (fun n q => ⟨(next n q).choose, (next n q).choose_spec.2⟩)
  exact ⟨fun n => (lifted n).val, rfl, fun n => (next n (lifted n)).choose_spec.1⟩

theorem infinite_iff (m : Matches f g R) {a : P} {b : Q} (related : R a b) :
    f.Infinite a ↔ g.Infinite b :=
  ⟨fun run => m.infinite_forward run related, fun run => m.symm.infinite_forward run related⟩

end Matches

theorem Matches.outcomes_iff {f : Graph P O} {g : Graph Q O} {a : P} {b : Q}
    (m : Matches f g R) (related : R a b) (sameDiv : f.divergence = g.divergence) (o : O)
    (terminal : ∀ {p q}, R p q → (f.finish p o ↔ g.finish q o)) :
    o ∈ f.outcomes a ↔ o ∈ g.outcomes b :=
  or_congr (m.finite_iff terminal related) (and_congr (by rw [sameDiv]) (m.infinite_iff related))

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

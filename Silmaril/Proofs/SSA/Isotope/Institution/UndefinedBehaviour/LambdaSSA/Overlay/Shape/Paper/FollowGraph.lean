module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

universe u w x

structure Jump (α : Type w) (σ : Type x) where
  label : Nat
  payload : Value α
  state : σ

inductive Exit (α : Type w) (σ : Type x) where
  | ret (label : Nat) (payload : Value α) (state : σ)
  | fault (state : σ)
  | diverge

variable {Φ : Type u} {α : Type w} {σ : Type x}
  {instr : Φ → Value α → σ → Value α → σ → Prop}
  {faults : Φ → Value α → σ → σ → Prop}
  {prim : Φ → Value α → σ → Prop}
  {env : Env α} {n : Nat} {bs : Fin n → Region Φ}

/-- The native follow relation as an ordinary graph. A local execution
either transfers to another block or emits an external observation. -/
@[expose] def followGraph (instr : Φ → Value α → σ → Value α → σ → Prop)
    (faults : Φ → Value α → σ → σ → Prop) (prim : Φ → Value α → σ → Prop)
    (env : Env α) (bs : Fin n → Region Φ) : Graph (Jump α σ) (Exit α σ) where
  step p q := ∃ hi : p.label < n, q.label < n ∧
    Semantics.Region.Eval instr (extend env p.payload) (bs ⟨p.label, hi⟩) p.state q.label q.payload q.state
  ub _ := False
  finish p
    | .ret j v t =>
        (n ≤ p.label ∧ p.label - n = j ∧ p.payload = v ∧ p.state = t) ∨
        ∃ hi : p.label < n,
          Semantics.Region.Eval instr (extend env p.payload) (bs ⟨p.label, hi⟩) p.state (n + j) v t
    | .fault t => ∃ hi : p.label < n,
        Semantics.Region.Fault instr faults (extend env p.payload) (bs ⟨p.label, hi⟩) p.state t
    | .diverge => ∃ hi : p.label < n,
        External.Diverges instr prim (.region (extend env p.payload) (bs ⟨p.label, hi⟩) p.state)
  divergence := .diverge

local notation "G" => followGraph instr faults prim env bs

theorem follow_ret {p : Jump α σ} {j : Nat} {a : Value α} {t : σ} :
    (G : Graph (Jump α σ) (Exit α σ)).Finite p (.ret j a t) ↔
      Semantics.Region.Follow instr env bs p.label p.payload p.state j a t := by
  constructor
  · rintro ⟨q, reach, finish⟩
    induction reach using Relation.ReflTransGen.head_induction_on with
    | refl =>
      rcases finish with ⟨hi, rfl, rfl, rfl⟩ | ⟨hi, run⟩
      · exact .exit hi
      · refine .step hi run ?_
        simpa only [Nat.add_sub_cancel_left] using
          (Semantics.Region.Follow.exit (blocks := bs) (Nat.le_add_right n j))
    | head step _ ih =>
      obtain ⟨hi, _, run⟩ := step
      exact .step hi run ih
  · cases p with
    | mk i v s =>
      intro run
      change Semantics.Region.Follow instr env bs i v s j a t at run
      induction run using Semantics.Region.Follow.rec (motive_1 := fun _ _ _ _ _ _ _ => True) with
      | exit outside => exact ⟨_, .refl, Or.inl ⟨outside, rfl, rfl, rfl⟩⟩
      | @step env n label next out blocks current middle value s s₁ s₂ inside head rest _ ih =>
        by_cases h : next < n
        · obtain ⟨q, path, finish⟩ := ih
          exact ⟨q, path.head ⟨inside, h, head⟩, finish⟩
        · cases rest with
          | exit outside =>
            exact ⟨_, .refl, Or.inr ⟨inside, by simpa only [Nat.add_sub_of_le outside] using head⟩⟩
          | step inside _ _ => exact (h inside).elim
      | _ => trivial

theorem follow_fault {p : Jump α σ} {t : σ} :
    (G : Graph (Jump α σ) (Exit α σ)).Finite p (.fault t) ↔
      Semantics.Region.FollowFault instr faults env bs p.label p.payload p.state t := by
  constructor
  · rintro ⟨q, reach, finish⟩
    induction reach using Relation.ReflTransGen.head_induction_on with
    | refl => obtain ⟨hi, run⟩ := finish; exact .body hi run
    | head step _ ih => obtain ⟨hi, _, run⟩ := step; exact .step hi run ih
  · cases p with
    | mk i v s =>
      intro run
      change Semantics.Region.FollowFault instr faults env bs i v s t at run
      induction run using Semantics.Region.FollowFault.rec (motive_1 := fun _ _ _ _ _ => True) with
      | body inside fault _ => exact ⟨_, .refl, ⟨inside, fault⟩⟩
      | step inside head rest ih =>
        obtain ⟨q, path, finish⟩ := ih
        have nextInside := by
          cases rest <;> assumption
        exact ⟨q, path.head ⟨inside, nextInside, head⟩, finish⟩
      | _ => trivial

private theorem serial_or_finite {P : Type w} {O : Type x} (g : Graph P O) {p : P}
    (live : P → Prop) (hp : live p)
    (unfold : ∀ q, live q → g.finish q g.divergence ∨ ∃ t, g.step q t ∧ live t) :
    g.Finite p g.divergence ∨ g.Infinite p := by
  classical
  by_cases finite : g.Finite p g.divergence
  · exact Or.inl finite
  · let Reachable := {q // g.Reaches p q ∧ live q}
    have next (q : Reachable) : ∃ t : Reachable, g.step q.val t.val := by
      rcases unfold q.val q.property.2 with finish | ⟨t, step, ht⟩
      · exact (finite ⟨q.val, q.property.1, finish⟩).elim
      · exact ⟨⟨t, q.property.1.tail step, ht⟩, step⟩
    let path : Nat → Reachable := Nat.rec ⟨p, .refl, hp⟩ (fun _ q => (next q).choose)
    exact Or.inr ⟨fun i => (path i).val, rfl, fun i => (next (path i)).choose_spec⟩

theorem follow_div {p : Jump α σ} :
    (G : Graph (Jump α σ) (Exit α σ)).Finite p .diverge ∨ (G).Infinite p ↔
      External.Diverges instr prim (.follow env bs p.label p.payload p.state) := by
  constructor
  · rintro (⟨q, reach, finish⟩ | ⟨path, start, edge⟩)
    · induction reach using Relation.ReflTransGen.head_induction_on with
      | refl =>
        obtain ⟨inside, div⟩ := finish
        exact .fold_core (.follow_body inside div)
      | head step _ ih =>
        obtain ⟨inside, _, head⟩ := step
        exact .fold_core (.follow_next inside head ih)
    · let runs (q : Jump α σ) :=
          Config.follow env bs q.label q.payload q.state
      have seed : Config.follow env bs p.label p.payload p.state = runs (path 0) :=
        congrArg runs start.symm
      refine External.Diverges.coinduct (fun c => ∃ i, c = runs (path i)) ?_ ⟨0, seed⟩
      rintro _ ⟨i, rfl⟩
      obtain ⟨inside, _, head⟩ := edge i
      exact .core (.follow_next inside head ⟨i + 1, rfl⟩)
  · intro div
    apply serial_or_finite G (fun q => External.Diverges instr prim (.follow env bs q.label q.payload q.state)) div
    intro q h
    cases h.unfold with
    | core step =>
      cases step with
      | follow_body inside div => exact .inl ⟨inside, div⟩
      | @follow_next _ _ _ next _ _ state _ payload inside head tail =>
        have nextInside : next < n := by cases tail.unfold with | core step => cases step <;> assumption
        exact .inr ⟨⟨next, payload, state⟩, ⟨inside, nextInside, head⟩, tail⟩

theorem follow_outcomes (p : Jump α σ) (o : Exit α σ) :
    o ∈ (G).outcomes p ↔
      match o with
      | .ret j a t => Semantics.Region.Follow instr env bs p.label p.payload p.state j a t
      | .fault t => Semantics.Region.FollowFault instr faults env bs p.label p.payload p.state t
      | .diverge => External.Diverges instr prim (.follow env bs p.label p.payload p.state) := by
  have same : (G).divergence = .diverge := rfl
  cases o with
  | ret j a t => simpa [Graph.outcomes, same] using (follow_ret (p := p) (j := j) (a := a) (t := t)
      (instr := instr) (faults := faults) (prim := prim) (env := env) (bs := bs))
  | fault t => simpa [Graph.outcomes, same] using (follow_fault (p := p) (t := t)
      (instr := instr) (faults := faults) (prim := prim) (env := env) (bs := bs))
  | diverge => simpa [Graph.outcomes, same] using (follow_div (p := p)
      (instr := instr) (faults := faults) (prim := prim) (env := env) (bs := bs))

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

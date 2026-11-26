module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Thms

/-! # Two-level closure of feedback graphs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

universe u v w x

/-- The graph of ordinary internal transfers, local UB, and ordinary terminal
observations. The result alphabet specifies its divergence observation. -/
structure Graph (P : Type u) (O : Type v) where
  step : P → P → Prop
  ub : P → Prop
  finish : P → O → Prop
  divergence : O

namespace Graph

variable {P : Type u} {O : Type v}

abbrev Reaches (g : Graph P O) := Relation.ReflTransGen g.step

def ReachesUB (g : Graph P O) (p : P) : Prop :=
  ∃ q, g.Reaches p q ∧ g.ub q

def Finite (g : Graph P O) (p : P) (o : O) : Prop :=
  ∃ q, g.Reaches p q ∧ g.finish q o

/-- An infinite path takes an ordinary transfer at every step. -/
def Infinite (g : Graph P O) (p : P) : Prop :=
  ∃ path : Nat → P, path 0 = p ∧ ∀ n, g.step (path n) (path (n + 1))

def outcomes (g : Graph P O) (p : P) : Set O :=
  {o | g.Finite p o ∨ o = g.divergence ∧ g.Infinite p}

noncomputable def close (g : Graph P O) (p : P) : WithTop (Set O) := by
  classical
  exact if g.ReachesUB p then ⊤ else ↑(g.outcomes p)

/-- An observation of a closed graph below fresh top. -/
def Ordinary (g : Graph P O) (p : P) (o : O) : Prop :=
  g.close p ≠ ⊤ ∧ o ∈ (g.close p).untopD Set.univ

/-- Hide transfers into inner points. A transfer to any other point becomes
an observable boundary outcome. Final observations keep their identity. -/
def inner (g : Graph P O) (inside : P → Prop) : Graph P (P ⊕ O) where
  step p q := g.step p q ∧ inside q
  ub := g.ub
  finish p
    | .inl q => g.step p q ∧ ¬ inside q
    | .inr o => g.finish p o
  divergence := .inr g.divergence

/-- Close the inner group first. The outer graph resumes only on ordinary
boundary outcomes. Inner UB becomes local UB, and inner infinite replay
becomes an ordinary divergence observation. -/
def outer (g : Graph P O) (inside : P → Prop) : Graph P O where
  step p q := (g.inner inside).Ordinary p (.inl q)
  ub p := (g.inner inside).close p = ⊤
  finish p o := (g.inner inside).Ordinary p (.inr o)
  divergence := g.divergence

/-- The graph view of overlay feedback has the same closed behaviour as
`Feedback.close`. Terminal labels are still the exact external labels. -/
def ofRun {τ : Type v} {R L : List τ} {α : Type w} {σ : Type x}
    (f : Run R L α σ) : Graph (Point R.length α σ) (Outcome L.length α σ) where
  step := Step f
  ub p := f p = ⊤
  finish p o := (f p).Ordinary (external R L o)
  divergence := .diverge

end Graph

/-- Partition the local block interface `I ++ O` at its inner prefix.
The entry and the outer blocks can be boundary points. -/
def insidePrefix {τ : Type v} (I O : List τ) {α : Type w} {σ : Type x} :
    Point (I ++ O).length α σ → Prop
  | .entry _ => False
  | .block i _ _ => i.val < I.length

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

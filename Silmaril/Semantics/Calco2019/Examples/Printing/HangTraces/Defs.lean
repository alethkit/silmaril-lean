module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Hangs.Thms

/-! # Nonempty trace sets with finite hangs -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.HangTraces

open Hangs

variable {A X Y : Type u}

attribute [local instance] seqAction

/-- Trace sets retain both finite failures and infinite output in the terminal summand. -/
abbrev Traces (A X : Type u) := {t : Set (Model A X) // t.Nonempty}

def prependWord (w : List A) (t : Model A X) : Model A X :=
  WriterAction.prependOutput w t

def extendSet (f : X → Set (Model A Y)) : Model A X → Set (Model A Y)
  | .inl (w, x) => prependWord w '' f x
  | .inr s => {.inr s}

def bindSet (p : Set (Model A X)) (f : X → Set (Model A Y)) : Set (Model A Y) :=
  {t | ∃ s ∈ p, t ∈ extendSet f s}

instance : Monad (Traces A) where
  pure x := ⟨{.inl ([], x)}, ⟨_, rfl⟩⟩
  bind p f := ⟨bindSet p.1 (fun x => (f x).1), by
    obtain ⟨s, hs⟩ := p.2
    rcases s with ⟨w, x⟩ | seq
    · obtain ⟨t, ht⟩ := (f x).2
      exact ⟨prependWord w t, _, hs, t, ht, rfl⟩
    · exact ⟨.inr seq, _, hs, rfl⟩⟩

/-- A finite execution stops in a return or an explicit terminal observation. -/
inductive FiniteRun (f : X → Traces A (Y ⊕ X)) : X → Model A Y → Prop
  | ret {x w y} : .inl (w, .inl y) ∈ (f x).1 → FiniteRun f x (.inl (w, y))
  | stop {x seq} : .inr seq ∈ (f x).1 → FiniteRun f x (.inr seq)
  | step {x z w t} : .inl (w, .inr z) ∈ (f x).1 → FiniteRun f z t →
      FiniteRun f x (prependWord w t)

/-- Every edge is a recursive return. Its word may be empty. -/
structure InfiniteRun (f : X → Traces A (Y ⊕ X)) (x : X) where
  state : ℕ → X
  word : ℕ → List A
  start : state 0 = x
  edge (i : ℕ) : .inl (word i, .inr (state (i+1))) ∈ (f (state i)).1

/-- Finite prefixes of the concatenated words. -/
def wordsPrefix (w : ℕ → List A) : ℕ → List A
  | 0 => []
  | n+1 => w 0 ++ wordsPrefix (fun i => w (i+1)) n

/-- A letter at a given position is observed if any finite prefix contains it. -/
def LetterAt (w : ℕ → List A) (n : ℕ) (a : A) : Prop :=
  ∃ k, (wordsPrefix w k)[n]? = some a

noncomputable def chunkAt (w : ℕ → List A) (n : ℕ) : Option A := by
  classical
  exact if h : ∃ a, LetterAt w n a then some h.choose else none

/-- Infinite recursion contributes precisely the characters emitted in finite time. -/
def InfiniteRun.realizes {f : X → Traces A (Y ⊕ X)} {x : X}
    (p : InfiniteRun f x) (t : Model A Y) : Prop :=
  ∃ s : Stream'.Seq A, t = .inr s ∧ ∀ n, s.get? n = chunkAt p.word n

def Runs (f : X → Traces A (Y ⊕ X)) (x : X) (t : Model A Y) : Prop :=
  FiniteRun f x t ∨ ∃ p : InfiniteRun f x, p.realizes t

end Silmaril.Calco2019.Examples.Printing.HangTraces

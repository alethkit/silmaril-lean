module

public import Mathlib.Data.QPF.Univariate.Basic
public import Mathlib.Data.Set.Countable
public import Silmaril.Semantics.Calco2019.Examples.SetModels.Nonempty.Thms

/-! # The countable nonempty powerset for printing and I/O -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.CountableResumption

open SetModels

/-- The base monad for the countably branching resumptions in §1.2. -/
abbrev Choice (X : Type u) := {p : NonemptyPowerset X // p.1.run.Countable}

namespace Choice

variable {X Y : Type u}

def outcomes (p : Choice X) : Set X := p.1.1.run

theorem countable (p : Choice X) : p.outcomes.Countable := p.2

theorem nonempty (p : Choice X) : p.outcomes.Nonempty := p.1.2

def ofSet (s : Set X) (hn : s.Nonempty) (hc : s.Countable) : Choice X :=
  ⟨⟨s, hn⟩, hc⟩

def ofRange (f : ℕ → X) : Choice X :=
  ofSet (Set.range f) ⟨f 0, Set.mem_range_self 0⟩ (Set.countable_range f)

instance : Monad Choice where
  pure x := ⟨pure x, Set.countable_singleton x⟩
  bind p f := ⟨p.1 >>= fun x => (f x).1, by
    have eq : (p.1 >>= fun x => (f x).1).1.run =
        ⋃ x ∈ p.outcomes, (f x).outcomes := by
      ext y
      simp only [Set.mem_iUnion, NonemptyPowerset.val_bind, Elgot.Nondet.mem_bind_iff, outcomes]
      exact ⟨fun ⟨x, hx, hy⟩ => ⟨x, hx, hy⟩, fun ⟨x, hx, hy⟩ => ⟨x, hx, hy⟩⟩
    rw [eq]
    exact p.countable.biUnion (fun x _ => (f x).countable)⟩

@[simp] theorem val_pure (x : X) : (pure x : Choice X).1 = pure x := rfl

@[simp] theorem val_bind (p : Choice X) (f : X → Choice Y) :
    (p >>= f).1 = p.1 >>= fun x => (f x).1 := rfl

end Choice
end Silmaril.Calco2019.Examples.CountableResumption

namespace Silmaril.Calco2019.Examples.CountableResumption

/-- A signature step returns a result or emits a label and waits for its reply. -/
abbrev Step {A : Type u} (B : A → Type u) (X Z : Type u) := X ⊕ ((a : A) × (B a → Z))

/-- A resumption layer makes a countable nonempty choice of returns or I/O steps. -/
abbrev Layer {A : Type u} (B : A → Type u) (X Z : Type u) := Choice (Step B X Z)

def stepMap {A X Z W : Type u} {B : A → Type u} (f : Z → W) :
    Step B X Z → Step B X W
  | .inl x => .inl x
  | .inr ⟨a, k⟩ => .inr ⟨a, f ∘ k⟩

/- A polynomial enumerates the countable alternatives. Its positions at an I/O
alternative are exactly the replies for that label. -/
namespace Enumeration

variable {A X : Type u} (B : A → Type u)

def slots : X ⊕ A → Type u
  | .inl _ => PEmpty
  | .inr a => B a

def polynomial (X : Type u) : PFunctor.{u, u} where
  A := ℕ → X ⊕ A
  B shape := (i : ℕ) × slots B (shape i)

def pack {Z : Type u} (tag : X ⊕ A) : (slots B tag → Z) → Step B X Z :=
  match tag with
  | .inl x => fun _ => .inl x
  | .inr a => fun k => .inr ⟨a, k⟩

def tag {Z : Type u} : Step B X Z → X ⊕ A
  | .inl x => .inl x
  | .inr ⟨a, _⟩ => .inr a

def reply {Z : Type u} (t : Step B X Z) : slots B (tag B t) → Z :=
  match t with
  | .inl _ => PEmpty.elim
  | .inr ⟨_, k⟩ => k

theorem pack_reply {Z : Type u} (t : Step B X Z) : pack B (tag B t) (reply B t) = t := by
  cases t <;> rfl

theorem pack_map {Z W : Type u} (f : Z → W) (s : X ⊕ A) (k : slots B s → Z) :
    pack B s (f ∘ k) = stepMap f (pack B s k) := by
  cases s <;> rfl

def abs {Z : Type u} (p : polynomial B X Z) : Layer B X Z :=
  Choice.ofRange fun i => pack B (p.1 i) fun r => p.2 ⟨i, r⟩

noncomputable def enumerate {Z : Type u} (p : Layer B X Z) : ℕ → Step B X Z :=
  (p.countable.exists_eq_range p.nonempty).choose

theorem enumerate_range {Z : Type u} (p : Layer B X Z) :
    p.outcomes = Set.range (enumerate B p) :=
  (p.countable.exists_eq_range p.nonempty).choose_spec

noncomputable def repr {Z : Type u} (p : Layer B X Z) : polynomial B X Z :=
  ⟨fun i => tag B (enumerate B p i), fun s => reply B (enumerate B p s.1) s.2⟩

end Enumeration

end Silmaril.Calco2019.Examples.CountableResumption

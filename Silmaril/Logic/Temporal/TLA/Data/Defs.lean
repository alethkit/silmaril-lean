module

/-!
# Sets and choice for TLA+

All values in a model share one carrier and equality is Lean equality.
Set formation takes an existing set as a bound, except for finite enumeration.
The choice policy is fixed by the model. See `docs/projects/tla-data.md`.
-/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Data

universe u

/-- Hilbert choice on value predicates, with a value even when a predicate has no witness. -/
structure ChoicePolicy (V : Type u) where
  choose : (V → Prop) → V
  witness : ∀ {p : V → Prop}, (∃ x, p x) → p (choose p)

namespace ChoicePolicy

variable {V : Type u}

/-- Classical choice with a model-fixed value for an unsatisfiable predicate. -/
noncomputable def classical (fallback : V) : ChoicePolicy V :=
  open Classical in
  { choose := fun p => if h : ∃ x, p x then Classical.choose h else fallback
    witness := fun h => by simpa [h] using Classical.choose_spec h }

/-- The value of choice on the everywhere-false predicate. -/
def noWitness (policy : ChoicePolicy V) : V := policy.choose (fun _ => False)

end ChoicePolicy

/-- A pure-set model for the set operations and choice of TLA+. -/
structure Model (V : Type u) where
  mem : V → V → Prop
  empty : V
  insert : V → V → V
  sep : V → (V → Prop) → V
  image : V → (V → V) → V
  sUnion : V → V
  powerset : V → V
  choice : ChoicePolicy V
  ext : ∀ {s t}, (∀ x, mem x s ↔ mem x t) → s = t
  notMem_empty : ∀ x, ¬ mem x empty
  mem_insert : ∀ {x a s}, mem x (insert a s) ↔ x = a ∨ mem x s
  mem_sep : ∀ {x s p}, mem x (sep s p) ↔ mem x s ∧ p x
  mem_image : ∀ {x s f}, mem x (image s f) ↔ ∃ y, mem y s ∧ f y = x
  mem_sUnion : ∀ {x s}, mem x (sUnion s) ↔ ∃ t, mem t s ∧ mem x t
  mem_powerset : ∀ {x s}, mem x (powerset s) ↔ ∀ y, mem y x → mem y s

namespace Model

variable {V : Type u}

/-- A list supplies the elements of a set enumeration. -/
def enum (M : Model V) (values : List V) : V :=
  values.foldr M.insert M.empty

def subset (M : Model V) (s t : V) : Prop :=
  ∀ x, M.mem x s → M.mem x t

def union (M : Model V) (s t : V) : V :=
  M.sUnion (M.enum [s, t])

def inter (M : Model V) (s t : V) : V :=
  M.sep s (fun x => M.mem x t)

def diff (M : Model V) (s t : V) : V :=
  M.sep s (fun x => ¬ M.mem x t)

/-- Unbounded rigid existential quantification ranges over the whole carrier. -/
def existsValue (_ : Model V) (p : V → Prop) : Prop := ∃ x, p x

/-- Unbounded rigid universal quantification ranges over the whole carrier. -/
def forallValue (_ : Model V) (p : V → Prop) : Prop := ∀ x, p x

def existsIn (M : Model V) (s : V) (p : V → Prop) : Prop :=
  M.existsValue (fun x => M.mem x s ∧ p x)

def forallIn (M : Model V) (s : V) (p : V → Prop) : Prop :=
  M.forallValue (fun x => M.mem x s → p x)

def choose (M : Model V) (p : V → Prop) : V := M.choice.choose p

def chooseIn (M : Model V) (s : V) (p : V → Prop) : V :=
  M.choose (fun x => M.mem x s ∧ p x)

end Model
end Silmaril.Logic.Temporal.TLA.Data

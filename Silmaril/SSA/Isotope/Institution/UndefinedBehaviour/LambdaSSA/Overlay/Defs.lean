module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Defs
public import Mathlib.Order.WithBot
public import Mathlib.Logic.Relation

/-! # A region UB overlay for exact LambdaSSA

Native regions retain their operational semantics. The overlay adds an explicit
UB region at each interface, sequencing through typed label continuations,
and feedback through a prefix of internal labels.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay

open Institution.Observational

universe u v w x

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ]

/-- An independent typed syntax. The continuation for a label binds its argument
before the enclosing value context. -/
inductive Region (Φ : Type u) {τ : Type v} [TypeFormers τ] [HasTy Φ τ] :
    VCtx τ → LCtx τ → Type (max u v) where
  | native {Γ L} (r : UB.Typed (Φ := Φ) Γ L) : Region Φ Γ L
  | ub {Γ L} : Region Φ Γ L
  | lsubst {Γ L K} (r : Region Φ Γ L) (k : (i : Fin L.length) → Region Φ (L.get i :: Γ) K) :
      Region Φ Γ K
  | feedback {Γ R L} (entry : Region Φ Γ (R ++ L))
      (blocks : (i : Fin R.length) → Region Φ (R.get i :: Γ) (R ++ L)) : Region Φ Γ L

/-- An observation from a fixed initial state. Returns are indexed by a label
in the exact interface. Payloads use the existing observational value carrier. -/
inductive Outcome (labels : Nat) (α : Type w) (σ : Type x) where
  | ret (label : Fin labels) (value : Value α) (final : σ)
  | fault (final : σ)
  | diverge

namespace Outcome

variable {n m : Nat} {α : Type w} {σ : Type x}

/-- Restore the initial state and the positional label of a native observation. -/
def observation (s : σ) : Outcome n α σ → Observation (Nat × Value α) σ
  | .ret i a s' => .ret s (i.val, a) s'
  | .fault s' => .fault s s'
  | .diverge => .diverge s

/-- Ordinary relational sequencing at one initial state. Faults and divergence
pass through. A return calls the continuation at its label, payload and final state. -/
def bind (p : Set (Outcome n α σ)) (k : Fin n → Value α → σ → Set (Outcome m α σ)) :
    Set (Outcome m α σ) :=
  {o | (match o with
        | .ret _ _ _ => False
        | .fault s' => .fault s' ∈ p
        | .diverge => .diverge ∈ p) ∨
    ∃ i a s, .ret i a s ∈ p ∧ o ∈ k i a s}

end Outcome

/-- Lift the subset order with a fresh greatest element at each initial state.
Even an ordinary universal set retains its identity as an ordinary behaviour. -/
abbrev Behaviour (labels : Nat) (α : Type w) (σ : Type x) :=
  WithTop (Set (Outcome labels α σ))

namespace Behaviour

variable {n m : Nat} {α : Type w} {σ : Type x}

/-- The ordinary outcomes permitted by a lifted behaviour. -/
def possible (p : Behaviour n α σ) : Set (Outcome n α σ) :=
  p.untopD Set.univ

/-- An outcome of an ordinary behaviour; the projected outcomes of fresh top
do not count as execution steps. -/
def Ordinary (p : Behaviour n α σ) (o : Outcome n α σ) : Prop :=
  p ≠ ⊤ ∧ o ∈ p.possible

/-- Top passes through sequencing. A continuation contributes UB only if the
source can reach it with that payload and state. -/
noncomputable def bind (p : Behaviour n α σ) (k : Fin n → Value α → σ → Behaviour m α σ) :
    Behaviour m α σ := by
  classical
  exact if p = ⊤ ∨ ∃ i a s, .ret i a s ∈ p.possible ∧ k i a s = ⊤ then ⊤
    else ↑(Outcome.bind p.possible fun i a s => (k i a s).possible)

end Behaviour

namespace Feedback

/-- An entry state or a block invocation with its incoming payload and state. -/
inductive Point (n : Nat) (α : Type w) (σ : Type x) where
  | entry (state : σ)
  | block (label : Fin n) (value : Value α) (state : σ)

variable {R L : List τ} {α : Type w} {σ : Type x}

/-- The local behaviour at each point, before processing its outgoing label. -/
abbrev Run (R L : List τ) (α : Type w) (σ : Type x) :=
  Point R.length α σ → Behaviour (R ++ L).length α σ

def run (entry : σ → Behaviour (R ++ L).length α σ)
    (blocks : Fin R.length → Value α → σ → Behaviour (R ++ L).length α σ) :
    Run R L α σ
  | .entry s => entry s
  | .block i a s => blocks i a s

/-- Lift an internal label into the combined label interface. -/
def internal (R L : List τ) (i : Fin R.length) : Fin (R ++ L).length :=
  (i.castAdd L.length).cast (@List.length_append _ R L).symm

/-- Lift an external outcome into the combined label interface. -/
def external (R L : List τ) : Outcome L.length α σ → Outcome (R ++ L).length α σ
  | .ret i a s => .ret ((i.natAdd R.length).cast (@List.length_append _ R L).symm) a s
  | .fault s => .fault s
  | .diverge => .diverge

/-- Follow a successful ordinary return into an internal block. -/
inductive Step (f : Run R L α σ) : Point R.length α σ → Point R.length α σ → Prop where
  | branch {p i a s} (ret : (f p).Ordinary (.ret (internal R L i) a s)) :
      Step f p (.block i a s)

/-- Zero or more ordinary internal transfers, including the entry point itself. -/
abbrev Reaches (f : Run R L α σ) := Relation.ReflTransGen (Step f)

/-- A finite ordinary path ending in the given external outcome. -/
def Finite (f : Run R L α σ) (p : Point R.length α σ) (o : Outcome L.length α σ) : Prop :=
  ∃ q, Reaches f p q ∧ (f q).Ordinary (external R L o)

/-- An actual infinite path of ordinary internal returns. -/
def Infinite (f : Run R L α σ) (p : Point R.length α σ) : Prop :=
  ∃ path : Nat → Point R.length α σ, path 0 = p ∧ ∀ j, Step f (path j) (path (j + 1))

/-- Some finite ordinary path exposes explicit UB. -/
def ReachesUB (f : Run R L α σ) (p : Point R.length α σ) : Prop :=
  ∃ q, Reaches f p q ∧ f q = ⊤

/-- The complete ordinary outcomes of feedback, including an infinite replay of
internal labels even when no individual step diverges. -/
def outcomes (f : Run R L α σ) (p : Point R.length α σ) : Set (Outcome L.length α σ) :=
  {o | Finite f p o ∨ o = .diverge ∧ Infinite f p}

/-- Close the internal labels of a graph at an initial point. -/
noncomputable def close (f : Run R L α σ) (p : Point R.length α σ) : Behaviour L.length α σ := by
  classical
  exact if ReachesUB f p then ⊤ else ↑(outcomes f p)

end Feedback

variable {Γ R L K : List τ}

/-- Implement an all-native substitution by one CFG. Each continuation block
can only jump out of the new CFG, so sequencing introduces no local cycle. -/
def nativeLsubst (r : UB.Typed (Φ := Φ) Γ L)
    (k : (i : Fin L.length) → UB.Typed (Φ := Φ) (L.get i :: Γ) K) : LambdaSSA.Region Φ :=
  .cfg r.val L.length (fun i => (k i).val.renameLabels (L.length + ·))

/-- The native recursive CFG with exactly the same connected label interface. -/
def nativeFeedback (entry : UB.Typed (Φ := Φ) Γ (R ++ L))
    (blocks : (i : Fin R.length) → UB.Typed (Φ := Φ) (R.get i :: Γ) (R ++ L)) :
    LambdaSSA.Region Φ :=
  .cfg entry.val R.length (fun i => (blocks i).val)

/-- Keep all primitive relations when binding an exit payload. -/
abbrev extendModel {n : Nat} (M : Model.{u,w,x} Φ n) (a : Value M.α) : Model.{u,w,x} Φ (n + 1) where
  α := M.α
  σ := M.σ
  instr := M.instr
  faults := M.faults
  prim := M.prim
  bound := LetIter.Semantics.extend M.bound a

/-- The original observations, restricted to the given initial state. -/
def nativeOutcomes (r : UB.Typed (Φ := Φ) Γ L) (M : Model.{u,w,x} Φ Γ.length) (s : M.σ) :
    Set (Outcome L.length M.α M.σ) :=
  {o | o.observation s ∈ UB.observe M r}

/-- Native atoms use the original observations, at the same bound environment.
Only successful exits invoke a continuation. -/
noncomputable def denote : {Γ L : List τ} → (r : Region Φ Γ L) → (M : Model.{u,w,x} Φ Γ.length) →
    M.σ → Behaviour L.length M.α M.σ
  | _, _, .native r, M, s => ↑(nativeOutcomes r M s)
  | _, _, .ub, _, _ => ⊤
  | _, _, .lsubst r k, M, s => (denote r M s).bind fun i a mid => denote (k i) (extendModel M a) mid
  | _, _, .feedback entry blocks, M, s =>
      Feedback.close
        (Feedback.run (denote entry M) (fun i a mid => denote (blocks i) (extendModel M a) mid))
        (.entry s)

/-- Interpret each component of typed feedback in its bound environment. -/
noncomputable abbrev feedbackRun (entry : Region Φ Γ (R ++ L))
    (blocks : (i : Fin R.length) → Region Φ (R.get i :: Γ) (R ++ L))
    (M : Model.{u,w,x} Φ Γ.length) : Feedback.Run R L M.α M.σ :=
  Feedback.run (denote entry M) (fun i a mid => denote (blocks i) (extendModel M a) mid)

/-- Project to the existing observations by expanding UB at each initial state. -/
def observe (r : Region Φ Γ L) (M : Model.{u,w,x} Φ Γ.length) :
    Set (Observation (Nat × Value M.α) M.σ) :=
  {o | ∃ s, o ∈ Outcome.observation s '' (denote r M s).possible}

/-- Refinement is pointwise over observational models and initial states, with
more permissive behaviours on the right. -/
def Refines (r t : Region Φ Γ L) : Prop :=
  ∀ (M : Model.{u,w,x} Φ Γ.length) (s : M.σ), denote r M s ≤ denote t M s

end Silmaril.Isotope.LambdaSSA.UB.Overlay

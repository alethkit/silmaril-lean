module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Defs
public import Mathlib.Order.WithBot

/-! # A region UB overlay for exact LambdaSSA

Native regions retain their operational semantics. The overlay adds an explicit
UB region at each interface and a constructor for sequencing through typed
label continuations.
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

/-- Top passes through sequencing. A continuation contributes UB only if the
source can reach it with that payload and state. -/
noncomputable def bind (p : Behaviour n α σ) (k : Fin n → Value α → σ → Behaviour m α σ) :
    Behaviour m α σ := by
  classical
  exact if p = ⊤ ∨ ∃ i a s, .ret i a s ∈ p.possible ∧ k i a s = ⊤ then ⊤
    else ↑(Outcome.bind p.possible fun i a s => (k i a s).possible)

end Behaviour

variable {Γ L K : List τ}

/-- Implement an all-native substitution by one CFG. Each continuation block
can only jump out of the new CFG, so sequencing introduces no local cycle. -/
def nativeLsubst (r : UB.Typed (Φ := Φ) Γ L)
    (k : (i : Fin L.length) → UB.Typed (Φ := Φ) (L.get i :: Γ) K) : LambdaSSA.Region Φ :=
  .cfg r.val L.length (fun i => (k i).val.renameLabels (L.length + ·))

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

/-- Project to the existing observations by expanding UB at each initial state. -/
def observe (r : Region Φ Γ L) (M : Model.{u,w,x} Φ Γ.length) :
    Set (Observation (Nat × Value M.α) M.σ) :=
  {o | ∃ s, o ∈ Outcome.observation s '' (denote r M s).possible}

/-- Refinement is pointwise over observational models and initial states, with
more permissive behaviours on the right. -/
def Refines (r t : Region Φ Γ L) : Prop :=
  ∀ (M : Model.{u,w,x} Φ Γ.length) (s : M.σ), denote r M s ≤ denote t M s

end Silmaril.Isotope.LambdaSSA.UB.Overlay

module

public import Silmaril.Semantics.Domain.Kleene
public import Silmaril.Semantics.Domain.Product

/-! # Ranked equation systems in a pointed ω-cpo

A path records a finite observation of the regular tree unfolded by an
equation system. Partial observations give a pointed ω-cpo in which the
equations can be interpreted by ordinary least fixed points.
-/

@[expose] public section

universe u v w z

namespace Silmaril.Calco2019.IterationTheory

open OmegaCompletePartialOrder Silmaril.Semantics.Domain

/-- A ranked signature of operations, each with finitely many arguments. -/
structure Signature where
  Symbol : Type u
  arity : Symbol → Nat

/-- The head of one equation after variable-only chains have been resolved. -/
inductive Head (σ : Signature.{u}) (P : Type v) (S : Type w)
  | bottom
  | exit (p : P)
  | node (a : σ.Symbol) (child : Fin (σ.arity a) → S)

/-- A deterministic system with exits from the given parameter set. -/
abbrev System (σ : Signature.{u}) (P : Type v) (S : Type w) := S → Head σ P S

/-- Partial labels at every finite path. The pointwise order permits
observations to be revealed monotonically. -/
abbrev PathDomain (σ : Signature.{u}) (P : Type v) :=
  List Nat → Part (σ.Symbol ⊕ P)

variable {σ : Signature.{u}} {P : Type v} {S : Type w} {T : Type z}

/-- Observe a system by following the given finite sequence of arguments. -/
def observe (g : System σ P S) (s : S) : PathDomain σ P
  | [] =>
    match g s with
    | .bottom => ⊥
    | .exit p => Part.some (.inr p)
    | .node a _ => Part.some (.inl a)
  | k :: path =>
    match g s with
    | .node a child =>
      if h : k < σ.arity a then observe g (child ⟨k, h⟩) path else ⊥
    | _ => ⊥

/-- Interpret a system as a continuous self-map on tuples of observations.
The arguments of an operation use the corresponding child's path domain. -/
noncomputable def update (g : System σ P S) : (S → PathDomain σ P) →𝒄 (S → PathDomain σ P) :=
  piHom fun s => piHom fun path =>
    match g s, path with
    | .exit p, [] => ContinuousHom.const (Part.some (.inr p))
    | .node a _, [] => ContinuousHom.const (Part.some (.inl a))
    | .node a child, k :: tail =>
      if h : k < σ.arity a then (evalHom (P := fun _ : List Nat => Part (σ.Symbol ⊕ P)) tail).comp
        (evalHom (P := fun _ : S => PathDomain σ P) (child ⟨k, h⟩))
      else ContinuousHom.const ⊥
    | _, _ => ContinuousHom.const ⊥

/-- Matched heads have the same labels and related corresponding children. -/
inductive HeadMatch (R : S → T → Prop) : Head σ P S → Head σ P T → Prop
  | bottom : HeadMatch R .bottom .bottom
  | exit (p : P) : HeadMatch R (.exit p) (.exit p)
  | node (a : σ.Symbol) (left : Fin (σ.arity a) → S) (right : Fin (σ.arity a) → T)
      (rel : ∀ i, R (left i) (right i)) : HeadMatch R (.node a left) (.node a right)

/-- Related states have matched heads. -/
def Bisimulation (g : System σ P S) (h : System σ P T) (R : S → T → Prop) : Prop :=
  ∀ s t, R s t → HeadMatch R (g s) (h t)

/-- Rename only the recursive states in an equation. -/
def Head.mapState (f : S → T) : Head σ P S → Head σ P T
  | .bottom => .bottom
  | .exit p => .exit p
  | .node a child => .node a (f ∘ child)

/-- A state map that preserves the head, parameter, and ordered arguments. -/
def PreservesEquations (g : System σ P S) (h : System σ P T) (f : S → T) : Prop :=
  ∀ s, (g s).mapState f = h (f s)

end Silmaril.Calco2019.IterationTheory

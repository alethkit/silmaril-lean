module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs

/-!
# Explicit φ view of λSSA branch arguments

A successor is a leaf of an existing λSSA terminator. The source and the path
to that leaf identify a transfer occurrence, even when two leaves name the
same label. This view transposes the arguments of branches that carry
right-associated tuples of typed variables, ending in unit.
-/

@[expose] public section

namespace Silmaril.SSA.PhiView

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (At Terminator Tm VCtx)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x

variable {Φ : Type u} {τ : Type v} {Source : Type w}

/-- The path to a branch leaf of an existing terminator. -/
inductive Successor : Terminator Φ → Type u where
  | jump {label : Nat} {arg : Tm Φ} : Successor (.br label arg)
  | left {discr : Tm Φ} {l r : Terminator Φ} : Successor l → Successor (.case discr l r)
  | right {discr : Tm Φ} {l r : Terminator Φ} : Successor r → Successor (.case discr l r)

def Successor.target : {term : Terminator Φ} → Successor term → Nat
  | .br label _, .jump => label
  | _, .left s | _, .right s => s.target

def Successor.argument : {term : Terminator Φ} → Successor term → Tm Φ
  | .br _ arg, .jump => arg
  | _, .left s | _, .right s => s.argument

/-- Case typing metadata supplies the scope at each branch leaf. The source
context is the context after the source block's statements. -/
inductive CaseTyping [TypeFormers τ] [HasTy Φ τ] : VCtx τ → Terminator Φ → Type (max u v) where
  | jump {Γ : VCtx τ} {label : Nat} {arg : Tm Φ} : CaseTyping Γ (.br label arg)
  | case {Γ : VCtx τ} {discr : Tm Φ} {l r : Terminator Φ} {A B : τ}
      (typed : discr.HasType Γ (Silmaril.coprod A B))
      (left : CaseTyping (A :: Γ) l) (right : CaseTyping (B :: Γ) r) :
      CaseTyping Γ (.case discr l r)

def CaseTyping.scope [TypeFormers τ] [HasTy Φ τ] {Γ : VCtx τ} {term : Terminator Φ}
    (typing : CaseTyping Γ term) (successor : Successor term) : VCtx τ :=
  match typing, successor with
  | .jump, .jump => Γ
  | .case _ l _, .left s => l.scope s
  | .case _ _ r, .right s => r.scope s

/-- Source identity and successor occurrence are distinct from the target label. -/
structure EdgeOcc (terms : Source → Terminator Φ) where
  source : Source
  successor : Successor (terms source)

variable {terms : Source → Terminator Φ}

def EdgeOcc.target (e : EdgeOcc terms) : Nat := e.successor.target

def EdgeOcc.argument (e : EdgeOcc terms) : Tm Φ := e.successor.argument

abbrev Incoming (terms : Source → Terminator Φ) (label : Nat) :=
  { e : EdgeOcc terms // e.target = label }

variable [TypeFormers τ] [HasTy Φ τ]

/-- Metadata for the source contexts of the existing terminators. -/
structure SourceTyping (terms : Source → Terminator Φ) where
  context : Source → VCtx τ
  cases : (source : Source) → CaseTyping (context source) (terms source)

def SourceTyping.scope (typing : SourceTyping (τ := τ) terms) (e : EdgeOcc terms) : VCtx τ :=
  (typing.cases e.source).scope e.successor

/-- A variable in scope at the branch leaf, with the requested parameter type. -/
abbrev Operand (Γ : VCtx τ) (A : τ) := { i : Nat // At Γ i A }

abbrev Arguments (Γ : VCtx τ) (types : List τ) :=
  (i : Fin types.length) → Operand Γ types[i]

def packedType : List τ → τ
  | [] => Silmaril.unit
  | A :: types => Silmaril.product A (packedType types)

def packTerm {Γ : VCtx τ} : {types : List τ} → Arguments Γ types → Tm Φ
  | [], _ => .unit
  | _ :: _, args => .pair (.var (args 0).val) (packTerm (fun i => args i.succ))

/-- Read every argument in the same pre-transfer environment. -/
def readArguments {α : Type x} {Γ : VCtx τ} :
    {types : List τ} → Arguments Γ types → Env α → Value α
  | [], _, _ => .unit
  | _ :: _, args, old => .pair (old (args 0).val) (readArguments (fun i => args i.succ) old)

variable (typing : SourceTyping (τ := τ) terms) (params : Nat → List τ)

/-- An admitted block-argument presentation certifies the packed argument of
each existing terminator leaf. In particular, every occurrence has a column. -/
abbrev BlockArgs :=
  (e : EdgeOcc terms) →
    { args : Arguments (typing.scope e) (params e.target) // packTerm args = e.argument }

/-- Destination-oriented φ operands, indexed by parameter and incoming occurrence. -/
abbrev Table :=
  (label : Nat) → (i : Fin (params label).length) → (e : Incoming terms label) →
    Operand (typing.scope e.val) (params label)[i]

variable {typing params}

/-- Collect the operands of the selected occurrence in destination parameter order. -/
def Table.column (table : Table typing params) (e : EdgeOcc terms) :
    Arguments (typing.scope e) (params e.target) :=
  fun i => table e.target i ⟨e, rfl⟩

/-- Emit an ordinary λSSA branch at the selected occurrence. This is also
available to producers of new tables, before certifying agreement with syntax. -/
def Table.branch (table : Table typing params) (e : EdgeOcc terms) : Terminator Φ :=
  .br e.target (packTerm (table.column e))

/-- A table that presents the arguments of the existing terminators. -/
structure View (typing : SourceTyping (τ := τ) terms) (params : Nat → List τ) where
  table : Table typing params
  packed : ∀ e, packTerm (table.column e) = e.argument

def ofBlockArgs (args : BlockArgs typing params) : View typing params := by
  refine ⟨?_, ?_⟩
  · intro _ i ⟨e, target⟩
    cases target
    exact (args e).val i
  · exact fun e => (args e).property

def toBlockArgs (view : View typing params) : BlockArgs typing params :=
  fun e => ⟨view.table.column e, view.packed e⟩

/-- The tuple latched at the selected edge, ready to bind as the destination
block's single packed λSSA parameter. All reads precede that binding. -/
def latch {α : Type x} (view : View typing params) (e : EdgeOcc terms) (old : Env α) : Value α :=
  readArguments (view.table.column e) old

end Silmaril.SSA.PhiView

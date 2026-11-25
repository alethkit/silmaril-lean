module

public import Silmaril.Logic.Temporal.TLA.Defs

/-! # Scoped General TLA

The binders follow §8.2 and Fig. 9 of Lamport's *The Temporal Logic of Actions*.
Sorts have fixed Lean carriers. State expressions and actions are denotational
leaves with separate rigid and flexible environments.
-/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.General

universe u v

variable {Sorts : Type u}

abbrev Context (Sorts : Type u) := Sorts → Type u

namespace Context

/-- Extend a context by a fresh variable of sort `a`. -/
abbrev bind (Γ : Context Sorts) (a : Sorts) : Context Sorts := fun s => Γ s ⊕ PLift (s = a)

def old {Γ : Context Sorts} {a s : Sorts} (x : Γ s) : Γ.bind a s := .inl x
def fresh (Γ : Context Sorts) (a : Sorts) : Γ.bind a a := .inr ⟨rfl⟩

abbrev Rename (Γ Δ : Context Sorts) := ∀ s, Γ s → Δ s

namespace Rename

variable {Γ Δ Ξ : Context Sorts}

def id (Γ : Context Sorts) : Rename Γ Γ := fun _ x => x
def comp (f : Rename Γ Δ) (g : Rename Δ Ξ) : Rename Γ Ξ := fun s x => g s (f s x)

def under (f : Rename Γ Δ) (a : Sorts) : Rename (Γ.bind a) (Δ.bind a) :=
  fun s x => match x with
    | .inl i => .inl (f s i)
    | .inr e => .inr e

def Injective (f : Rename Γ Δ) : Prop :=
  ∀ s ⦃x y⦄, f s x = f s y → x = y

end Rename
end Context

abbrev Valuation (Value : Sorts → Type u) (Γ : Context Sorts) := ∀ s, Γ s → Value s

namespace Valuation

variable {Value : Sorts → Type u} {Γ Δ : Context Sorts}

def restrict (f : Context.Rename Γ Δ) (v : Valuation Value Δ) : Valuation Value Γ :=
  fun s x => v s (f s x)

def extend (v : Valuation Value Γ) {a : Sorts} (w : Value a) : Valuation Value (Γ.bind a) :=
  fun _ x => match x with
    | .inl i => v _ i
    | .inr ⟨e⟩ => e.symm ▸ w

def drop {a : Sorts} (v : Valuation Value (Γ.bind a)) : Valuation Value Γ :=
  fun _ x => v _ (Context.old x)

def last {a : Sorts} (v : Valuation Value (Γ.bind a)) : Value a :=
  v a (Γ.fresh a)

end Valuation

structure Scope (Sorts : Type u) where
  rigid : Context Sorts
  flex : Context Sorts

namespace Scope

abbrev bindRigid (Γ : Scope Sorts) (a : Sorts) : Scope Sorts := ⟨Γ.rigid.bind a, Γ.flex⟩
abbrev bindFlex (Γ : Scope Sorts) (a : Sorts) : Scope Sorts := ⟨Γ.rigid, Γ.flex.bind a⟩

/-- A sort-preserving map of free names, independently in the two contexts. -/
structure Rename (Γ Δ : Scope Sorts) where
  rigid : Context.Rename Γ.rigid Δ.rigid
  flex : Context.Rename Γ.flex Δ.flex

namespace Rename

variable {Γ Δ Ξ : Scope Sorts}

def id (Γ : Scope Sorts) : Rename Γ Γ := ⟨Context.Rename.id _, Context.Rename.id _⟩
def comp (f : Rename Γ Δ) (g : Rename Δ Ξ) : Rename Γ Ξ :=
  ⟨f.rigid.comp g.rigid, f.flex.comp g.flex⟩

def underRigid (f : Rename Γ Δ) (a : Sorts) : Rename (Γ.bindRigid a) (Δ.bindRigid a) :=
  ⟨f.rigid.under a, f.flex⟩

def underFlex (f : Rename Γ Δ) (a : Sorts) : Rename (Γ.bindFlex a) (Δ.bindFlex a) :=
  ⟨f.rigid, f.flex.under a⟩

end Rename
end Scope

variable {Value : Sorts → Type u} {Γ Δ : Scope Sorts}

abbrev RigidEnv (Value : Sorts → Type u) (Γ : Scope Sorts) := Valuation Value Γ.rigid
abbrev State (Value : Sorts → Type u) (Γ : Scope Sorts) := Valuation Value Γ.flex

/-- A rigid environment and a behavior of flexible states. -/
structure Model (Value : Sorts → Type u) (Γ : Scope Sorts) where
  rigid : RigidEnv Value Γ
  behavior : Behavior (State Value Γ)

def Model.reduct (f : Scope.Rename Γ Δ) (M : Model Value Δ) : Model Value Γ :=
  ⟨M.rigid.restrict f.rigid, M.behavior.map (Valuation.restrict f.flex)⟩

abbrev Expr (Value : Sorts → Type u) (Γ : Scope Sorts) (X : Type v) :=
  RigidEnv Value Γ → StateExpr (State Value Γ) X

namespace Expr

def rigid {a : Sorts} (x : Γ.rigid a) : Expr Value Γ (Value a) := fun ρ _ => ρ a x
def flex {a : Sorts} (x : Γ.flex a) : Expr Value Γ (Value a) := fun _ s => s a x

def rename {X : Type v} (e : Expr Value Γ X) (f : Scope.Rename Γ Δ) : Expr Value Δ X :=
  fun ρ s => e (ρ.restrict f.rigid) (s.restrict f.flex)

end Expr

/-- Both ends of an action use the same rigid environment. Use
`TLA.Action.current` and `TLA.Action.prime` on a state expression at that environment. -/
abbrev Action (Value : Sorts → Type u) (Γ : Scope Sorts) :=
  RigidEnv Value Γ → TLA.Action (State Value Γ)

namespace Action

def rename (A : Action Value Γ) (f : Scope.Rename Γ Δ) : Action Value Δ :=
  fun ρ s t => A (ρ.restrict f.rigid) (s.restrict f.flex) (t.restrict f.flex)

def existsRigid {a : Sorts} (A : Action Value (Γ.bindRigid a)) : Action Value Γ :=
  fun ρ s t => ∃ v : Value a, A (ρ.extend v) s t

end Action

/-- State-level syntax keeps `ENABLED` explicit so renaming an enabled action
evaluates its successors in the new scope. -/
inductive StatePred (Value : Sorts → Type u) : Scope Sorts → Type (u + 1) where
  | atom {Γ : Scope Sorts} (p : Expr Value Γ Prop) : StatePred Value Γ
  | enabled {Γ : Scope Sorts} (A : Action Value Γ) : StatePred Value Γ
  | neg {Γ : Scope Sorts} (p : StatePred Value Γ) : StatePred Value Γ
  | conj {Γ : Scope Sorts} (p q : StatePred Value Γ) : StatePred Value Γ
  | existsRigid {Γ : Scope Sorts} (a : Sorts) (p : StatePred Value (Γ.bindRigid a)) : StatePred Value Γ

namespace StatePred

def rename {Γ Δ : Scope Sorts} (f : Scope.Rename Γ Δ) : StatePred Value Γ → StatePred Value Δ
  | .atom p => .atom (p.rename f)
  | .enabled A => .enabled (A.rename f)
  | .neg p => .neg (p.rename f)
  | .conj p q => .conj (p.rename f) (q.rename f)
  | .existsRigid a p => .existsRigid a (p.rename (f.underRigid a))

def eval {Γ : Scope Sorts} : StatePred Value Γ → RigidEnv Value Γ → State Value Γ → Prop
  | .atom p, ρ, s => p ρ s
  | .enabled A, ρ, s => (A ρ).enabled s
  | .neg p, ρ, s => ¬ p.eval ρ s
  | .conj p q, ρ, s => p.eval ρ s ∧ q.eval ρ s
  | .existsRigid a p, ρ, s => ∃ v : Value a, p.eval (ρ.extend v) s

end StatePred

/-- Scoped temporal syntax. The body of either binder has one extra variable
of its specified sort. Rigid and flexible binders extend different contexts. -/
inductive Formula (Value : Sorts → Type u) : Scope Sorts → Type (u + 1) where
  | state {Γ : Scope Sorts} (p : StatePred Value Γ) : Formula Value Γ
  | alwaysBracket {Γ : Scope Sorts} {X : Type u} (A : Action Value Γ)
      (e : Expr Value Γ X) : Formula Value Γ
  | neg {Γ : Scope Sorts} (p : Formula Value Γ) : Formula Value Γ
  | conj {Γ : Scope Sorts} (p q : Formula Value Γ) : Formula Value Γ
  | always {Γ : Scope Sorts} (p : Formula Value Γ) : Formula Value Γ
  | existsRigid {Γ : Scope Sorts} (a : Sorts) (p : Formula Value (Γ.bindRigid a)) : Formula Value Γ
  | existsFlex {Γ : Scope Sorts} (a : Sorts) (p : Formula Value (Γ.bindFlex a)) : Formula Value Γ

namespace Formula

def rename {Γ Δ : Scope Sorts} (f : Scope.Rename Γ Δ) : Formula Value Γ → Formula Value Δ
  | .state p => .state (p.rename f)
  | .alwaysBracket A e => .alwaysBracket (A.rename f) (e.rename f)
  | .neg p => .neg (p.rename f)
  | .conj p q => .conj (p.rename f) (q.rename f)
  | .always p => .always (p.rename f)
  | .existsRigid a p => .existsRigid a (p.rename (f.underRigid a))
  | .existsFlex a p => .existsFlex a (p.rename (f.underFlex a))

def Sat {Γ : Scope Sorts} :
    Formula Value Γ → RigidEnv Value Γ → Behavior (State Value Γ) → Prop
  | .state p, ρ, σ => p.eval ρ (σ 0)
  | .alwaysBracket A e, ρ, σ => (TLA.Formula.alwaysBracket (A ρ) (e ρ)).Sat σ
  | .neg p, ρ, σ => ¬ p.Sat ρ σ
  | .conj p q, ρ, σ => p.Sat ρ σ ∧ q.Sat ρ σ
  | .always p, ρ, σ => ∀ n, p.Sat ρ (σ.suffix n)
  | .existsRigid a p, ρ, σ => ∃ v : Value a, p.Sat (ρ.extend v) σ
  | .existsFlex _ p, ρ, σ => hide (fun τ => p.Sat ρ (τ.map fun z => z.1.extend z.2)) σ

def Holds (p : Formula Value Γ) (ρ : RigidEnv Value Γ) (σ : Behavior (State Value Γ))
    (n : Nat) : Prop := p.Sat ρ (σ.suffix n)

def Satisfies (p : Formula Value Γ) (M : Model Value Γ) : Prop := p.Sat M.rigid M.behavior

def Entails (p q : Formula Value Γ) : Prop := ∀ M, p.Satisfies M → q.Satisfies M

def forallRigid (a : Sorts) (p : Formula Value (Γ.bindRigid a)) : Formula Value Γ :=
  .neg (.existsRigid a (.neg p))

def forallFlex (a : Sorts) (p : Formula Value (Γ.bindFlex a)) : Formula Value Γ :=
  .neg (.existsFlex a (.neg p))

def eventually (p : Formula Value Γ) : Formula Value Γ := .neg (.always (.neg p))

end Formula

/-- A semantic refinement maps each implementation state to a specification
state and transports satisfying behaviors by that map. -/
def Refines {S : Type u} {T : Type v} (implementation : Behavior S → Prop) (map : S → T)
    (specification : Behavior T → Prop) : Prop :=
  ∀ σ, implementation σ → specification (σ.map map)

end Silmaril.Logic.Temporal.TLA.General

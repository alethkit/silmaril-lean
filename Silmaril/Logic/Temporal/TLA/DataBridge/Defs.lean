module

public import Silmaril.Logic.Temporal.TLA.General.Defs

/-! # One-sorted denotations for TLA+ data

The carrier and the free name types are supplied by the caller. Rigid parameters
share one valuation across a step, and each endpoint has its own flexible valuation.
-/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.DataBridge

universe u v

abbrev DataSort := PUnit.{u + 1}

abbrev Carrier (V : Type u) : DataSort.{u} → Type u := fun _ => V

/-- The free scope uses independent name types for rigid and flexible coordinates. -/
abbrev scope (Rigid Flex : Type u) : General.Scope DataSort.{u} :=
  ⟨fun _ => Rigid, fun _ => Flex⟩

abbrev RigidEnv (V : Type u) (Γ : General.Scope DataSort.{u}) := General.RigidEnv (Carrier V) Γ
abbrev State (V : Type u) (Γ : General.Scope DataSort.{u}) := General.State (Carrier V) Γ

/-- An expression may return a carrier value or a Lean observation of another type. -/
abbrev StateExpr (V : Type u) (Γ : General.Scope DataSort.{u}) (X : Type v) :=
  General.Expr (Carrier V) Γ X

abbrev StatePredicate (V : Type u) (Γ : General.Scope DataSort.{u}) := StateExpr V Γ Prop

/-- A step expression returning `Prop` is definitionally a `General.Action`. -/
abbrev StepExpr (V : Type u) (Γ : General.Scope DataSort.{u}) (X : Type v) :=
  RigidEnv V Γ → State V Γ → State V Γ → X

variable {V : Type u} {Γ : General.Scope DataSort.{u}} {X : Type v}

/-- Read an entire state expression at the source, including state predicates used as actions. -/
def current (e : StateExpr V Γ X) : StepExpr V Γ X :=
  fun ρ => TLA.Action.current (e ρ)

/-- Read an entire state expression at the target with the same rigid valuation. -/
def prime (e : StateExpr V Γ X) : StepExpr V Γ X :=
  fun ρ => TLA.Action.prime (e ρ)

def unchanged (observe : StateExpr V Γ X) : General.Action (Carrier V) Γ :=
  fun ρ => TLA.Action.unchanged (observe ρ)

def bracket (A : General.Action (Carrier V) Γ) (observe : StateExpr V Γ X) :
    General.Action (Carrier V) Γ :=
  fun ρ => TLA.Action.bracket (A ρ) (observe ρ)

end Silmaril.Logic.Temporal.TLA.DataBridge

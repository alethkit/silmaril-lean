module

public import Silmaril.Logic.Temporal.TLA.DataBridge.Defs

public section

namespace Silmaril.Logic.Temporal.TLA.DataBridge

universe u v

variable {V : Type u} {Γ : General.Scope DataSort.{u}} {X : Type v}

theorem current_apply (e : StateExpr V Γ X) (ρ : RigidEnv V Γ) (s t : State V Γ) :
    current e ρ s t = e ρ s := rfl

theorem prime_apply (e : StateExpr V Γ X) (ρ : RigidEnv V Γ) (s t : State V Γ) :
    prime e ρ s t = e ρ t := rfl

theorem state_holds (p : StatePredicate V Γ) (ρ : RigidEnv V Γ)
    (σ : Behavior (State V Γ)) (n : Nat) :
    (General.Formula.state (.atom p)).Holds ρ σ n ↔ p ρ (σ n) := Iff.rfl

theorem unchanged_iff (observe : StateExpr V Γ X) (ρ : RigidEnv V Γ) (s t : State V Γ) :
    unchanged observe ρ s t ↔ observe ρ t = observe ρ s := Iff.rfl

theorem bracket_iff (A : General.Action (Carrier V) Γ) (observe : StateExpr V Γ X)
    (ρ : RigidEnv V Γ) (s t : State V Γ) :
    bracket A observe ρ s t ↔ A ρ s t ∨ observe ρ t = observe ρ s := Iff.rfl

end Silmaril.Logic.Temporal.TLA.DataBridge

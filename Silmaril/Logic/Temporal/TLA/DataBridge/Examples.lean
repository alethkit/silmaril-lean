module

import Silmaril.Logic.Temporal.TLA.DataBridge.Thms

/-! A predicate-valued observation used directly by a scoped General TLA formula. -/

namespace Silmaril.Logic.Temporal.TLA.DataBridge.Examples

private abbrev NatSet := Nat → Prop

private inductive FlexName where
  | contents
  | scratch

private abbrev Γ := scope Unit FlexName

private def visible : StateExpr NatSet Γ NatSet :=
  fun ρ s n => ρ PUnit.unit () n ∧ s PUnit.unit .contents n

private def clear : General.Action (Carrier NatSet) Γ :=
  fun ρ s t => ∀ n, ¬ prime visible ρ s t n

private def spec : General.Formula (Carrier NatSet) Γ := .alwaysBracket clear visible

private def rigid : RigidEnv NatSet Γ := fun _ _ _ => True

private def run : Behavior (State NatSet Γ) :=
  fun i _ name n => match name with
    | .contents => n = 0
    | .scratch => i = 0

/-- The bracket holds by observation equality while scratch changes. -/
example : spec.Sat rigid run := fun _ _ => Or.inr rfl

example : ¬ clear rigid (run 0) (run 1) :=
  fun h => h 0 ⟨True.intro, rfl⟩

example : run 0 ≠ run 1 := by
  intro h
  have same : (0 = 0) = (1 = 0) :=
    congrArg (fun s : State NatSet Γ => s PUnit.unit .scratch 0) h
  exact Nat.noConfusion (same.mp rfl)

end Silmaril.Logic.Temporal.TLA.DataBridge.Examples

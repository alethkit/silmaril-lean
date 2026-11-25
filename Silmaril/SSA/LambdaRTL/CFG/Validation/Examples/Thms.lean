module

public import Silmaril.SSA.LambdaRTL.CFG.Validation.Thms
public import Mathlib.Logic.Equiv.Basic

/-! Kernel-checked success and a counterexample to dropping the relay's
parameter guard. Both examples use the existing forward CFG evaluator. -/

@[expose] public section
namespace Silmaril.SSA.LambdaRTL.CFG.Validation.Examples

private abbrev Graph := CFG Bool Nat Empty

private def source (argument : Bool) : Graph :=
  ⟨.term (.br 11 (.var argument)),
    [(11, ⟨false, .term (.br 12 (.var false))⟩),
     (12, ⟨false, .term (.br 99 (.var false))⟩)]⟩

private def target : Graph :=
  ⟨.term (.br 12 (.var false)), [(12, ⟨false, .term (.br 99 (.var false))⟩)]⟩

private def view (label : Nat) : Bool := label == 99
private def rename : Nat ≃ Nat := Equiv.swap 11 21
private def renamed : Graph := (source false).relabel rename

private theorem rename_preserves : PreservesView view rename := by
  intro label
  by_cases h11 : label = 11
  · subst label
    decide
  by_cases h21 : label = 21
  · subst label
    decide
  simp [rename, Equiv.swap_apply_def, h11, h21]

private theorem accepted : contractEntry? renamed = some target := by decide

private theorem related : (source false, target) ∈ close (cfgIso view) := by
  have first : (source false, renamed) ∈ cfgIso view := ⟨rename, rename_preserves, rfl⟩
  have next : EntryRelay renamed target := contractEntry_sound accepted
  exact (Relation.ReflTransGen.single (.inl first)).tail (.inr next)

private def model : Model Empty Option Nat where
  unit := 0
  pair a _ := a
  inl := id
  inr := id
  unpair _ := none
  split _ := none
  app op _ := op.elim
  abort _ := none

private def store (x : Bool) : Nat := if x then 7 else 3

private def result (graph : Graph) : Option (Nat × Nat × Nat) :=
  (fun out => (out.1, out.2.1, out.2.2 false)) <$> graph.run model store

/-- Renaming and contracting may be combined while preserving the visible exit,
payload and complete register store in the institution. -/
example : (Institution.rtlFullRoom Bool Nat Option Nat
      (fun a b => observe view <$> a = observe view <$> b) ⟨Empty⟩).Sat
    (CategoryTheory.Discrete.mk model) ⟨∅, (source false).toRegion, target.toRegion⟩ :=
  region_satisfies view model ∅ ⟨source false, target, related, rfl, rfl⟩

example : result (source false) = some (99, 3, 3) := by decide
example : result target = some (99, 3, 3) := by decide

-- The edge is still 11, but passing `true` overwrites `false` and changes the exit payload.
example : contractEntry? (source true) = none := by decide
example : result (source true) = some (99, 7, 7) := by decide
example : ¬ PreservesView view (Equiv.swap 11 99) := by
  intro h
  have distinct : view ((Equiv.swap 11 99) 11) ≠ view 11 := by decide
  exact distinct (h 11)

end Silmaril.SSA.LambdaRTL.CFG.Validation.Examples

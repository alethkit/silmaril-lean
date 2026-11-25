module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Thms

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA

/-! A continuation can discard the expression passed by raw label substitution.
The example observes whether a unit-valued instruction advances a counter. -/

namespace LambdaSSAEffectfulReplacement

local instance : HasTy Unit (Ty Empty) where
  src _ := .unit
  trg _ := .unit

private def entry : Region Unit := .br 0 (.op () .unit)
private def keep : Nat → Region Unit := fun _ => .let₁ (.var 0) (.br 0 .unit)
private def drop : Nat → Region Unit := fun _ => .br 0 .unit

example : Region.HasType ([] : VCtx (Ty Empty)) entry [.unit] := .br rfl (.op .unit)

theorem continuations_equivalent :
    Region.LSubst.Equivalent ([] : VCtx (Ty Empty)) [.unit] [.unit] keep drop := by
  intro ℓ A hi
  cases ℓ with
  | zero =>
      cases Option.some.inj hi
      exact .letBr (.var rfl) .unit rfl
  | succ ℓ => simp [At] at hi

private def tick (_ : Unit) (input : Value Empty) (before : Nat)
    (output : Value Empty) (after : Nat) : Prop :=
  output = input ∧ after = before + 1

private def env : Semantics.Env Empty := fun _ => .unit

private theorem tick_deterministic : Semantics.InstrDeterministic tick := by
  intro f input start r s r' s' h h'
  exact ⟨h.1.trans h'.1.symm, h.2.trans h'.2.symm⟩

theorem entry_substituted_keep :
    Semantics.Region.Eval tick env (entry.lsubst keep) 0 0 .unit 1 :=
  .let₁ (.op .unit ⟨rfl, rfl⟩) (.br .unit)

theorem entry_substituted_drop :
    ¬ Semantics.Region.Eval tick env (entry.lsubst drop) 0 0 .unit 1 := by
  have h₀ : Semantics.Region.Eval tick env (entry.lsubst drop) 0 0 .unit 0 := .br .unit
  intro h₁
  exact Nat.zero_ne_one (h₀.deterministic tick_deterministic h₁).2.2

/-- Binding the argument before literal substitution runs the producer once. -/
theorem bound_substitution_keeps_effect :
    Semantics.Region.Eval tick env (entry.bindBranchArguments.lsubst drop) 0 0 .unit 1 := by
  unfold entry
  rw [Region.lsubst_bindBranchArguments_br]
  exact .let₁ (.op .unit ⟨rfl, rfl⟩) (.br .unit)

/-- The same effect is retained by the linked CFG with a dropping continuation. -/
theorem linked_continuation_keeps_effect :
    Semantics.Region.Eval tick env (entry.linkExits ([.unit] : LCtx (Ty Empty)) drop) 0 0 .unit 1 := by
  change Semantics.Region.Eval tick env (.cfg entry 1 (fun _ => .br 1 .unit)) 0 0 .unit 1
  exact .cfg (.br (.op .unit ⟨rfl, rfl⟩))
    (.step (by decide) (.br .unit) (.exit (by decide : 1 ≤ 1)))

end LambdaSSAEffectfulReplacement

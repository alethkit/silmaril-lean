module

import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Thms
meta import Silmaril.SSA.Isotope.Types.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Defs

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Regression

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open TwoBlock.TwoExit (callCase)
open Silmaril.Elgot (iter)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private abbrev Ty := Silmaril.Ty Unit
private abbrev number : Ty := .base ()
private abbrev innerPayload : Ty := .product number number

@[reducible] private def Value : Ty → Type
  | .base _ => Nat
  | .product a b => Value a × Value b
  | .unit => PUnit
  | .coprod a b => Value a ⊕ Value b
  | .empty => PEmpty

private def coerceValue {A B : Ty} : Isotope.Ty.Subty A B → Value A → Value B
  | .refl _ => id
  | .trans f g => coerceValue g ∘ coerceValue f
  | .product f g => fun (a,b) => (coerceValue f a, coerceValue g b)
  | .coprod f g => Sum.map (coerceValue f) (coerceValue g)
  | .empty _ => PEmpty.elim
  | .unit _ => fun _ => PUnit.unit

local instance : TypeModel Ty where
  interp := Value
  productEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun x => by cases x; rfl, fun x => by cases x; rfl⟩
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, fun x => PEmpty.elim x, fun x => Empty.elim x⟩
  coe := coerceValue

private inductive Op | enter | inner | finish

local instance : HasTy Op Ty :=
  ⟨fun | .enter | .finish => number | .inner => innerPayload,
   fun | .enter => innerPayload | .inner => .coprod number innerPayload | .finish => .coprod number number⟩

local instance : HasEff Op Bool := ⟨fun _ => true⟩

private abbrev Runtime := StateT Nat Part
private def instruction : (op : Op) → Value (instrSrc op) → Runtime (Value (instrTrg op))
  | .enter, n => StateT.mk fun token => Part.some ((n, (0 : Nat)), 10 * token + 1)
  | .inner, (n, step) => StateT.mk fun token =>
    Part.some (if (show Nat from n) = 99 ∨ (show Nat from step) = 0 then .inr (n, (1 : Nat)) else .inl n,
      10 * token + 2)
  | .finish, n => StateT.mk fun token =>
    Part.some (if (show Nat from n) = 0 then .inr (1 : Nat) else .inl token, 10 * token + 3)

local instance : InstructionModel Op Ty Bool Runtime where
  denote := instruction
  denotePure _ h := False.elim (by change true = false at h; cases h)
  denote_pure _ h _ := False.elim (by change true = false at h; cases h)

private def op (f : Op) : TwoBlock.Instruction Op (instrSrc (τ := Ty) f) (instrTrg (τ := Ty) f) :=
  ⟨f, rfl, rfl⟩

private def program : Loop Op number innerPayload number number :=
  ⟨op .enter, op .inner, op .finish⟩

private def lowered := lower program
private abbrev Coherent := RegionCoherent (τ := Ty) (Φ := Op) (ε := Bool) (m := Runtime)

private theorem call_eq (f : Op) (x : Value (instrSrc f)) :
    TwoBlock.call (ε := Bool) (m := Runtime) (op f) x = instruction f x := by
  unfold TwoBlock.call
  change instruction f x >>= pure = _
  exact bind_pure _

private abbrev innerAction := callCase (ε := Bool) (m := Runtime) program.inner

private theorem inner_step (n step token : Nat) :
    Elgot.StateT.body innerAction ((n,step),token) =
      Part.some (if n = 99 ∨ step = 0 then .inr ((n,1),10 * token + 2) else .inl (n,10 * token + 2)) := by
  have action : innerAction = instruction .inner := by
    funext x
    change callCase (ε := Bool) (m := Runtime) (op .inner) x = instruction .inner x
    unfold callCase
    exact (congrArg (fun (v : Runtime (Value (.coprod number innerPayload))) => v >>= pure)
      (call_eq .inner x)).trans (bind_pure _)
  rw [action]
  by_cases repeatStep : n = 99 ∨ step = 0 <;>
    simp [repeatStep, instruction, Elgot.StateT.body, Elgot.StateT.distribute, Part.pure_eq_some]

private theorem inner_returns (n token : Nat) (allowed : n ≠ 99) :
    (iter innerAction ((n,0) : Value innerPayload)).run token =
      Part.some (n, 100 * token + 22) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.more (a' := ((n,1), 10 * token + 2))
  · rw [inner_step]
    simp
  · apply Elgot.Part.Runs.done
    rw [inner_step]
    simp [allowed]
    omega

private theorem inner_noReturn (step token : Nat) :
    (iter innerAction ((99,step) : Value innerPayload)).run token = Part.none := by
  have impossible {input : (Nat × Nat) × Nat} {out : Nat × Nat}
      (h : Elgot.Part.Runs (Elgot.StateT.body innerAction) input out) : input.1.1 ≠ 99 := by
    induction h with
    | @done current out result =>
      rcases current with ⟨⟨n, step⟩, token⟩
      intro eq
      change n = 99 at eq
      subst n
      rw [inner_step] at result
      simp at result
    | @more current next out result run ih =>
      rcases current with ⟨⟨n, step⟩, token⟩
      intro eq
      change n = 99 at eq
      subst n
      rw [inner_step] at result
      have nextEq : next = ((99,1),10 * token + 2) := by simpa using result
      exact ih (congrArg (fun p : (Nat × Nat) × Nat => p.1.1) nextEq)
  rw [Elgot.StateT.run_iter, Part.eq_none_iff]
  intro out h
  exact impossible ((Elgot.Part.mem_iter_iff _ _ _).mp h) rfl

private noncomputable abbrev roundAction := round (ε := Bool) (m := Runtime) program

private theorem round_run (n token : Nat) :
    (roundAction n).run token =
      if n = 99 then Part.none
      else Part.some ((if n = 0 then Sum.inr (1 : Nat) else Sum.inl (1000 * token + 122)),
        10000 * token + 1223) := by
  unfold roundAction round
  rw [show TwoBlock.call (ε := Bool) (m := Runtime) program.enter n =
    instruction .enter n from call_eq .enter _]
  have finish_eq (k : Nat) : callCase (ε := Bool) (m := Runtime) program.finish k = instruction .finish k := by
    unfold callCase
    rw [show TwoBlock.call (ε := Bool) (m := Runtime) program.finish k =
      instruction .finish k from call_eq .finish _]
    exact bind_pure _
  simp only [finish_eq, StateT.run_bind, Part.bind_eq_bind]
  change (((Part.some (((n,0) : Value innerPayload),10 * token + 1)).bind _).bind _) = _
  rw [Part.bind_some]
  change (((iter innerAction ((n,0) : Value innerPayload)).run (10 * token + 1)).bind _) = _
  by_cases blocked : n = 99
  · subst n
    rw [inner_noReturn]
    simp
  · rw [inner_returns _ _ blocked]
    simp only [blocked, ite_false, Part.bind_some]
    have beforeFinish : 100 * (10 * token + 1) + 22 = 1000 * token + 122 := by omega
    rw [beforeFinish]
    have afterFinish : 10 * (1000 * token + 122) + 3 = 10000 * token + 1223 := by omega
    change Part.some ((if n = 0 then Sum.inr (1 : Nat) else Sum.inl (1000 * token + 122)),
      10 * (1000 * token + 122) + 3) = _
    rw [afterFinish]

private theorem returning :
    (iter roundAction (0 : Nat)).run 0 = Part.some ((1223122 : Nat),12231223) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.more (a' := ((1 : Nat),1223))
  · apply Part.eq_some_iff.mp
    unfold Elgot.StateT.body
    simp [round_run, Elgot.StateT.distribute]
  · apply Elgot.Part.Runs.done
    apply Part.eq_some_iff.mp
    unfold Elgot.StateT.body
    simp [round_run, Elgot.StateT.distribute]

private theorem noReturn : (iter roundAction (99 : Nat)).run 0 = Part.none := by
  rw [Elgot.StateT.run_iter, Part.eq_none_iff]
  intro out h
  rw [Elgot.Part.mem_iter_iff] at h
  have noStep : Elgot.StateT.body roundAction ((99 : Nat),0) = Part.none := by
    unfold Elgot.StateT.body
    simp [round_run]
  cases h with
  | done h | more h _ => rw [noStep] at h; exact Part.notMem_none _ h

example (coherent : Coherent) :
    returns (ε := Bool) lowered.1 (0 : Nat) 0 (1223122 : Nat) 12231223 := by
  apply (lowered.2.region_returns_iff coherent (PUnit.unit, (0 : Nat)) (1223122 : Nat) 0 12231223).mpr
  rw [show lowered.2.typing = regionTyping program from rfl,
    denote_rounds program coherent (PUnit.unit, (0 : Nat)), StateT.run_bind, returning]
  simp only [StateT.run_pure, Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some]

example (coherent : Coherent) : observe (ε := Bool) lowered.1 (99 : Nat) 0 = Part.none := by
  apply (lowered.2.region_undefined_iff coherent (PUnit.unit, (99 : Nat)) 0).mpr
  rw [show lowered.2.typing = regionTyping program from rfl,
    denote_rounds program coherent (PUnit.unit, (99 : Nat)), StateT.run_bind, noReturn]
  exact Part.bind_none _

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Regression

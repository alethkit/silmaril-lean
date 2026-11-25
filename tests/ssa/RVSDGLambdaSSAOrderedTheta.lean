module

import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms
import Silmaril.Raw.SSA.Isotope.Semantics.Model

namespace Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Tests

open Silmaril.Elgot
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open OrderedRuntime.Structured

set_option backward.isDefEq.respectTransparency false

private abbrev Code := Silmaril.Ty Unit
private abbrev number : Code := .base ()
private abbrev Op := Option Nat
private abbrev Value := Silmaril.Ty.denote (fun _ : Unit => Nat)

private def coerce {A B : Code} : Isotope.Ty.Subty A B → Value A → Value B
  | .refl _ => id
  | .trans f g => coerce g ∘ coerce f
  | .product f g => fun (a, b) => (coerce f a, coerce g b)
  | .coprod f g => Sum.map (coerce f) (coerce g)
  | .empty _ => PEmpty.elim
  | .unit _ => fun _ => PUnit.unit

local instance : TypeModel Code where
  interp := Value
  productEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun x => by cases x; rfl, fun x => by cases x; rfl⟩
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, fun x => PEmpty.elim x, fun x => Empty.elim x⟩
  coe := coerce

local instance : HasTy Op Code := ⟨fun _ => number, fun _ => .coprod number number⟩
local instance : HasEff Op Bool := ⟨fun _ => true⟩

private def step (limit : Op) : Step Op number := ⟨limit, rfl, rfl⟩

private def advance (payload state : Nat) : Nat × Nat :=
  (payload + state + 2, state + payload + 1)

private def primitive (limit : Op) (payload : Nat) : StateM Nat (Nat ⊕ Nat) :=
  fun state =>
    let (next, updated) := advance payload state
    ((match limit with
        | none => .inr next
        | some bound => if updated < bound then .inr next else .inl next), updated)

local instance : InstructionModel Op Code Bool (StateT Nat Part) where
  denote op a := StateT.mk fun state => Part.some ((primitive op a).run state)
  denotePure op h := False.elim (by change true = false at h; cases h)
  denote_pure op h _ := False.elim (by change true = false at h; cases h)

private def total : Steps (τ := Code) Op (StateM Nat) := fun {_} s x =>
  fun state =>
    let (choice, updated) := (primitive s.op (cast (congrArg Value s.input.symm) x)).run state
    (Sum.map (fun y => cast (congrArg Value s.input) y) (fun y => cast (congrArg Value s.input) y) choice, updated)

private def lowered (limit : Op) := lower (SSAForm.loop (step limit))
private def raised (limit : Op) := raise (RVForm.loop (step limit))

private theorem agrees (limit : Op) :
    stepMap (ε := Bool) (m := StateT Nat Part) (lowered limit).2.step =
      liftState total (lowered limit).2.step := by
  funext input
  apply StateT.ext
  intro state
  change (stepMap (ε := Bool) (step limit) input : StateT Nat Part _).run state =
    (liftState total (step limit) input).run state
  simp only [stepMap, StateT.run_bind, StateT.run_pure]
  change (Part.some ((primitive limit input).run state)).bind (fun p => Part.some p) =
    (liftState total (step limit) input).run state
  rw [Part.bind_some]
  change Part.some ((primitive limit input).run state) =
    Part.some (Sum.map id id ((primitive limit input).run state).1,
      ((primitive limit input).run state).2)
  obtain ⟨choice, updated⟩ := (primitive limit input).run state
  cases choice <;> rfl

example : (lowered (some 10)).1 = graph (step (some 10)) := rfl
example : (raised (some 10)).1 = region (some 10) := rfl

example (limit : Op) :
    RegionDenotes (m := StateT Nat Part) Bool (raised limit).2.typing (fun env =>
      iter (stepMap (ε := Bool) (m := StateT Nat Part) (raised limit).2.step) env.2 >>=
        fun a => pure (exit a)) :=
  (raised limit).2.ssa_denotes

-- The state advances 0 → 2 → 6 → 14. The state at each back edge controls the
-- next payload and stopping test, so a state reset changes the result.
example :
    (iter (stepMap (ε := Bool) (m := StateT Nat Part) (lowered (some 10)).2.step) (1 : Nat)).run 0 =
      Part.some ((15 : Nat), 14) := by
  apply ((lowered (some 10)).2.returns_iff total (agrees _) (1 : Nat) (15 : Nat) 0 14).mpr
  exact .again (next := point (A := number) (3 : Nat) 2) rfl (.again (next := point (A := number) (7 : Nat) 6) rfl (.stop rfl))

private def trajectory (n : Nat) : Nat × Nat :=
  Nat.rec (1, 0) (fun _ p => advance p.1 p.2) n

example :
    (iter (stepMap (ε := Bool) (m := StateT Nat Part) (lowered none).2.step) (1 : Nat)).run 0 =
      Part.none := by
  apply ((lowered none).2.diverges_iff total (agrees _) (1 : Nat) 0).mpr
  exact ⟨fun i => point (trajectory i).1 (trajectory i).2, rfl, fun _ => rfl⟩

end Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Tests

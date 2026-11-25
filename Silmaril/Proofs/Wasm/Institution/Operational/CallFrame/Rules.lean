module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallFrame.Proofs

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution.Runtime (Value)

/-- The one-premise call rules use exactly the existing flat-locals derivations. -/
inductive Move (fn : Callee) : State → State → Prop where
  | fact {a b} (h : Ground fn a b) : Move fn a b
  | reduce (saved : List Value) {a b : Locals.State} (edge : Locals.Edge a b) :
      Move fn (.label saved a.locals (.code (.locals a.code)))
        (.label saved b.locals (.code (.locals b.code)))

theorem invert {fn : Callee} {a b : State} (edge : Edge fn a b) : Move fn a b := by
  refine Derives.least (M := fun j => match j with
    | .body (a, b) => Locals.Edge a b
    | .call a b => Move fn a b) edge ?_
  intro r hr ih
  change RuleInstance fn r at hr
  cases hr with
  | @body r h => exact .apply h (fun j hj => ih (.body j) (List.mem_map_of_mem hj))
  | reduce saved a b => exact .reduce saved (ih (.body (a, b)) (List.Mem.head _))
  | fact h => exact .fact h

theorem saved_of_live {fn : Callee} {a b : State} (edge : Edge fn a b)
    (live : ∀ xs, a ≠ .trapped xs) : b.saved = a.saved := by
  cases invert edge with
  | reduce => rfl
  | fact rule =>
    cases rule
    case bubble saved discarded _ => exact (live (saved ++ discarded) rfl).elim
    all_goals rfl

private theorem body_derives (fn : Callee) {a b : Locals.State} (step : Locals.Edge a b) :
    (presentation fn).Derives (.body (a, b)) := by
  refine Derives.least (M := fun j => (presentation fn).Derives (.body j)) step ?_
  intro r hr ih
  change Locals.RuleInstance r at hr
  refine Derives.apply (R := (presentation fn).rules)
    (r := ⟨r.premises.map .body, .body r.conclusion⟩) (RuleInstance.body hr) ?_
  intro j hj
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hj
  exact ih x hx

theorem reduce {fn : Callee} (saved : List Value) {a b : Locals.State} (step : Locals.Edge a b) :
    Edge fn (.label saved a.locals (.code (.locals a.code))) (.label saved b.locals (.code (.locals b.code))) :=
  Derives.apply (R := (presentation fn).rules)
    (r := ⟨[.body (a, b)], .call _ _⟩) (RuleInstance.reduce saved a b)
    (fun _ h => (List.mem_singleton.mp h).symm ▸ body_derives fn step)

private theorem check_values (types stack : List NumType) (vs : List Value) :
    Locals.check types stack (Locals.values vs) = some ((vs.map Value.type).reverse ++ stack) := by
  induction vs generalizing stack with
  | nil => rfl
  | cons v tail ih =>
    change Locals.check types (v.type :: stack) (Locals.values tail) = _
    rw [ih]
    simp

theorem closed {fn : Callee} {a b : State} (guard : Admitted fn a) (step : Edge fn a b) :
    Admitted fn b := by
  cases invert step with
  | reduce saved edge => exact Locals.closed guard edge
  | fact rule =>
    cases rule with
    | enter saved args arity =>
      have defaults : (fn.locals.map Value.zero).map Value.type = fn.locals := by
        rw [List.map_map]
        change fn.locals.map id = fn.locals
        simp
      exact ⟨by simp [Callee.init, Callee.localTypes, guard.1, defaults], guard.2⟩
    | unreachable => exact guard.1
    | labelValues saved ls stack =>
      obtain ⟨types, typed⟩ := guard
      change Locals.check fn.localTypes [] (Locals.values stack) = some fn.result.toList at typed
      rw [check_values] at typed
      exact ⟨types, by simpa using typed⟩
    | labelReturn => exact guard
    | labelTrap => exact guard
    | frameValues => exact guard.2
    | frameReturn saved ls extra results arity =>
      have typed := guard.2
      change ((extra ++ results).map Value.type).reverse.take fn.arity = _ at typed
      have length : (results.map Value.type).reverse.length = fn.arity := by simpa using arity
      change (results.map Value.type).reverse = fn.result.toList
      simpa [List.map_append, List.reverse_append, ← length, List.take_left] using typed
    | frameTrap | bubble => trivial

end Silmaril.Wasm.Institution.Operational.CallFrame.Proofs

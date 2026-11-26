module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run
open Core.Module (ListHeap)
open Core.Module.Functions (Session)
open Core.Module.SeededCall (Namespace)
open Core.Closure.Executor (CodeTable)

theorem ordinary_scalar_trace {scope : Source.Scope} (table : CodeTable) (session : Session)
    (actions : List (Compile.ModuleEntry.Action scope)) :
    ∃ reached completion,
      runPrefix table (actions.length + 1) (.ready session (actions.map .scalar)) =
        ([], .finished reached completion) ∧ reached.heap = session.heap ∧ reached.lists = session.lists := by
  induction actions generalizing session with
  | nil => exact ⟨session, .normal, rfl, rfl, rfl⟩
  | cons action rest tail =>
    cases action with
    | assign name reference operand =>
      cases evaluated : evaluate session operand with
      | error failure =>
        exact ⟨session, failure, by simp [runPrefix, advance, scalarStep, evaluated, Except.map], rfl, rfl⟩
      | ok value =>
        obtain ⟨reached, completion, finished, heap, lists⟩ := tail (session.bindGlobal name value)
        exact ⟨reached, completion, by simpa [runPrefix, advance, scalarStep, evaluated, Except.map] using finished, heap, lists⟩
    | assertion operand =>
      cases evaluated : evaluate session operand with
      | error failure =>
        exact ⟨session, failure, by simp [runPrefix, advance, scalarStep, checkAssertion, Except.bind, Except.map, evaluated], rfl, rfl⟩
      | ok value =>
        by_cases holds : Core.Module.Functions.truth value = true
        · obtain ⟨reached, completion, finished, heap, lists⟩ := tail session
          exact ⟨reached, completion, by simpa [runPrefix, advance, scalarStep, checkAssertion, Except.bind, Except.map, evaluated, holds] using finished,
            heap, lists⟩
        · exact ⟨session, .assertionError, by simp [runPrefix, advance, scalarStep, checkAssertion, Except.bind, Except.map, evaluated, holds], rfl, rfl⟩

theorem seeded_scalar_carriers {scope : Source.Scope} (space : Namespace) (context : Seeded.CallContext)
    (actions : List (Compile.ModuleEntry.Action scope)) (lists : ListHeap) :
    let outcome := Seeded.runInstructionsIn space context (actions.map .scalar) lists
    outcome.heap = context.heap ∧ outcome.lists = lists ∧ outcome.calls = [] ∧
      outcome.residual.builtins = space.builtins := by
  induction actions generalizing space with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons action rest tail =>
    cases action with
    | assign name reference operand =>
      cases evaluated : Seeded.evaluateScalar space false operand with
      | error failure =>
        simp [Seeded.runInstructionsIn, Seeded.effectWithLists, Seeded.effect, Seeded.scalarBinding, evaluated, Except.map, Except.mapError]
      | ok value =>
        simpa [Seeded.runInstructionsIn, Seeded.effectWithLists, Seeded.effect, Seeded.scalarBinding, evaluated, Except.map,
          Except.mapError, Core.Module.SeededCall.Namespace.bindGlobal] using tail (space.bindGlobal name value)
    | assertion operand =>
      cases evaluated : Seeded.evaluateScalar space false operand with
      | error failure =>
        simp [Seeded.runInstructionsIn, Seeded.effectWithLists, Seeded.effect, Seeded.scalarBinding, Seeded.assertOperand,
          evaluated, Except.bind, Except.map, Except.mapError]
      | ok value =>
        by_cases holds : Seeded.truth value = true
        · simpa [Seeded.runInstructionsIn, Seeded.effectWithLists, Seeded.effect, Seeded.scalarBinding, Seeded.assertOperand,
            Seeded.assertTruthAs, evaluated, holds, Except.bind, Except.map, Except.mapError] using tail space
        · simp [Seeded.runInstructionsIn, Seeded.effectWithLists, Seeded.effect, Seeded.scalarBinding, Seeded.assertOperand,
            Seeded.assertTruthAs, evaluated, holds, Except.bind, Except.map, Except.mapError]

open Compile.ModuleEntry.Functions.ExceptionalTry (Outcome Plan Step runSuite)

theorem runSuite_append {state failure action : Type}
    (step : state → action → Except failure state) (initial : state) (earlier later : List action) :
    runSuite step initial (earlier ++ later) =
      let first := runSuite step initial earlier
      match first.completion with
      | .ok () => runSuite step first.reached later
      | .error _ => first := by
  induction earlier generalizing initial with
  | nil => rfl
  | cons action rest ih =>
    cases first : step initial action <;> simp [runSuite, first, ih]

private theorem runSuite_preserves {state failure action : Type}
    (step : state → action → Except failure state) (property : state → Prop)
    (keeps : ∀ {input next act}, step input act = .ok next → property input → property next)
    (initial : state) (actions : List action) (started : property initial) :
    property (runSuite step initial actions).reached := by
  induction actions generalizing initial with
  | nil => exact started
  | cons action rest ih =>
    cases next : step initial action with
    | ok reached => simpa [runSuite, next] using ih reached (keeps next started)
    | error error => simpa [runSuite, next] using started

private theorem run_preserves {state failure action : Type}
    (step : state → action → Except failure state) (isPythonError : failure → Bool) (property : state → Prop)
    (keeps : ∀ {input next act}, step input act = .ok next → property input → property next)
    (initial : state) (plan : Plan action) (started : property initial) :
    property (Compile.ModuleEntry.Functions.ExceptionalTry.run (runSuite step) isPythonError initial plan).reached := by
  have suiteKeeps {before : state} (actions : List action) (holds : property before) :=
    runSuite_preserves step property keeps before actions holds
  unfold Compile.ModuleEntry.Functions.ExceptionalTry.run
  have afterBodyKeeps : property (runSuite step initial plan.body).reached :=
    suiteKeeps plan.body started
  have pendingKeeps : property
      (Compile.ModuleEntry.Functions.ExceptionalTry.afterBody (runSuite step) isPythonError
        (runSuite step initial plan.body) plan.handler plan.otherwise).reached := by
    unfold Compile.ModuleEntry.Functions.ExceptionalTry.afterBody
    split
    · exact suiteKeeps _ afterBodyKeeps
    · split
      · exact suiteKeeps _ afterBodyKeeps
      · exact afterBodyKeeps
    · exact afterBodyKeeps
  dsimp only
  unfold Compile.ModuleEntry.Functions.ExceptionalTry.runCleanup
  split
  · have cleaned := suiteKeeps plan.cleanup pendingKeeps
    unfold Outcome.afterCleanup
    split <;> exact cleaned
  · exact pendingKeeps

theorem ordinary_reached_carriers {scope : Source.Scope} (session : Session)
    (plan : Plan (Step scope)) :
    let outcome := Compile.ModuleEntry.Functions.Run.runExceptionalTry session plan
    outcome.reached.heap = session.heap ∧ outcome.reached.lists = session.lists := by
  refine run_preserves exceptionalStep Completion.isPythonError
    (fun reached => reached.heap = session.heap ∧ reached.lists = session.lists) ?_ session plan ⟨rfl, rfl⟩
  intro initial reached step done kept
  cases step with
  | raiseCall call => simp [exceptionalStep] at done
  | scalar action =>
    change Compile.ModuleEntry.Functions.Run.scalarStep initial action = .ok reached at done
    cases action with
    | assign name reference operand =>
      cases evaluated : evaluate initial operand <;> simp [Compile.ModuleEntry.Functions.Run.scalarStep, evaluated, Except.map] at done
      subst reached
      exact kept
    | assertion operand =>
      cases checked : checkAssertion initial operand true <;> simp [Compile.ModuleEntry.Functions.Run.scalarStep, checked, Except.map] at done
      subst reached
      exact kept

theorem seeded_reached_builtins {scope : Source.Scope} (space : Namespace)
    (plan : Plan (Step scope)) :
    (Seeded.runExceptionalTry space plan).reached.builtins = space.builtins := by
  refine run_preserves Seeded.exceptionalStep Seeded.ModuleFailure.isPythonError
    (fun reached => reached.builtins = space.builtins) ?_ space plan rfl
  intro initial reached step done kept
  cases step with
  | raiseCall call => simp [Seeded.exceptionalStep] at done
  | scalar action =>
    change Seeded.scalarStep initial action = .ok reached at done
    cases binding : Seeded.scalarBinding initial action with
    | error error => simp [Seeded.scalarStep, binding, Except.map] at done
    | ok update =>
      simp [Seeded.scalarStep, binding, Except.map] at done
      subst reached
      cases update with
      | none => exact kept
      | some pair =>
        obtain ⟨name, value⟩ := pair
        exact kept

theorem seeded_settlement {scope : Source.Scope} (space : Namespace) (context : Seeded.CallContext)
    (plan : Plan (Step scope)) (rest : List (Instruction scope)) (lists : ListHeap) :
    Seeded.runInstructionsIn space context (.exceptionalTry plan :: rest) lists =
      let outcome := Seeded.runExceptionalTry space plan
      match outcome.completion with
      | .ok () => Seeded.runInstructionsIn outcome.reached context rest lists
      | .error error => ⟨outcome.reached, .error error, [], context.heap, lists⟩ := by
  have reached : {space with moduleGlobals := (Seeded.runExceptionalTry space plan).reached.moduleGlobals} =
      (Seeded.runExceptionalTry space plan).reached := by
    have same := seeded_reached_builtins space plan
    generalize (Seeded.runExceptionalTry space plan).reached = residual at same ⊢
    cases space
    cases residual
    cases same
    rfl
  cases finished : (Seeded.runExceptionalTry space plan).completion <;>
    simp [Seeded.runInstructionsIn, Seeded.effectWithLists, Seeded.effect, Except.map, finished, reached]

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry

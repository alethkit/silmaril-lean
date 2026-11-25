module

public import Silmaril.Languages.Python.Compile.Closed.Defs
public import Silmaril.Languages.Python.Core.Thms

public section
namespace Silmaril.Proofs.Languages.Python.Compile.Closed

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closed
open Silmaril.Semantics.Operational

theorem lowerExpr_sound {source : Source.Expr} {target : Core.Expr}
    (accepted : lowerExpr source = .ok target) : ExprTranslation source target := by
  cases source <;> try simp [lowerExpr] at accepted
  case integer value =>
    subst target
    exact .integer value
  case binary operator left right =>
    cases operator <;> simp [lowerExpr] at accepted
    case add =>
      cases lhs : lowerExpr left with
      | error error => simp [Except.bind, lhs] at accepted
      | ok leftTarget =>
        cases rhs : lowerExpr right with
        | error error => simp [Except.bind, Except.map, lhs, rhs] at accepted
        | ok rightTarget =>
          simp [Except.bind, Except.map, lhs, rhs] at accepted
          subst target
          exact .add (lowerExpr_sound lhs) (lowerExpr_sound rhs)
termination_by sizeOf source

theorem lowerExpr_iff (source : Source.Expr) (target : Core.Expr) :
    lowerExpr source = .ok target ↔ ExprTranslation source target := by
  refine ⟨lowerExpr_sound, ?_⟩
  intro translated
  induction translated with
  | integer value => rfl
  | add leftTranslation rightTranslation leftExact rightExact =>
    simp [lowerExpr, Except.bind, Except.map, leftExact, rightExact]

theorem lower_iff (source : Source.Module) (target : Core.Body) :
    lower source = .ok target ↔ Translation source target := by
  constructor
  · intro accepted
    unfold lower at accepted
    split at accepted
    next name value =>
      cases lowered : lowerExpr value with
      | error error => simp [Except.map, lowered] at accepted
      | ok expr =>
        simp [Except.map, lowered] at accepted
        subst target
        exact .function name (lowerExpr_sound lowered)
    next => simp at accepted
  · intro translated
    cases translated with
    | function name translated => simp [lower, Except.map, (lowerExpr_iff _ _).mpr translated]

theorem compile_iff (source : Source.Module) (target : Core.Body) :
    compile source = .ok target ↔
      (∃ scope, Source.analyze source = .ok scope) ∧ Translation source target := by
  cases analyzed : Source.analyze source <;>
    simp [compile, analyzed, lower_iff]

theorem supports {source : Source.Expr} {target : Core.Expr}
    (translated : ExprTranslation source target) : Core.Profile.addition.supports target := by
  induction translated with
  | integer value => rfl
  | add leftTranslation rightTranslation leftSupported rightSupported =>
    simp [Core.Profile.supports, leftSupported, rightSupported]
    rfl

theorem eval_iff {source : Source.Expr} {target : Core.Expr}
    (translated : ExprTranslation source target) (result : Int) :
    Evaluates source result ↔ target.eval = .ok result := by
  induction translated generalizing result with
  | integer value =>
    constructor
    · intro evaluated
      cases evaluated
      rfl
    · intro evaluated
      have equal : value = result := Except.ok.inj evaluated
      subst result
      exact .integer value
  | @add left right lhs rhs _ _ leftEval rightEval =>
    constructor
    · intro evaluated
      cases evaluated with
      | add evalLeft evalRight =>
        simp [Core.Expr.eval, Except.bind, (leftEval _).mp evalLeft, (rightEval _).mp evalRight,
          Core.BinOp.eval]
    · intro evaluated
      cases leftValue : lhs.eval with
      | error error => simp [Core.Expr.eval, Except.bind, leftValue] at evaluated
      | ok a =>
        cases rightValue : rhs.eval with
        | error error => simp [Core.Expr.eval, Except.bind, leftValue, rightValue] at evaluated
        | ok b =>
          simp [Core.Expr.eval, Except.bind, leftValue, rightValue, Core.BinOp.eval] at evaluated
          subst result
          exact .add ((leftEval _).mpr leftValue) ((rightEval _).mpr rightValue)

theorem evaluates {source : Source.Expr} {target : Core.Expr}
    (translated : ExprTranslation source target) : ∃ result, Evaluates source result := by
  induction translated with
  | integer value => exact ⟨value, .integer value⟩
  | add _ _ left right =>
    obtain ⟨lhs, hLeft⟩ := left
    obtain ⟨rhs, hRight⟩ := right
    exact ⟨lhs + rhs, .add hLeft hRight⟩

theorem returns_exists {source : Source.Module} {body : Core.Body}
    (translated : Translation source body) : ∃ result, Returns source result := by
  cases translated with
  | function name translated =>
    obtain ⟨result, resultEval⟩ := evaluates translated
    exact ⟨result, .function name resultEval⟩

theorem observes {source : Source.Module} {body : Core.Body} {result : Int}
    (translated : Translation source body) :
    (Core.model .addition).May body (.returned (.ok result)) ↔ Returns source result := by
  cases translated with
  | function name translated =>
    rw [Core.model_may_iff]
    constructor
    · rintro ⟨_, equal⟩
      have evaluated := (eval_iff translated result).mpr (by simpa using equal.symm)
      exact .function name evaluated
    · intro returned
      cases returned with
      | function _ evaluated =>
        exact ⟨supports translated, by simp [(eval_iff translated result).mp evaluated]⟩

theorem run_exact {source : Source.Module} {body : Core.Body} {result : Int} {fuel : Nat}
    (translated : Translation source body) (evaluated : Returns source result)
    (enough : body.start.budget ≤ fuel) :
    Core.run .addition body fuel =
      some (.stop (.finished (.ok result)) (.observed (.returned (.ok result)))) := by
  have ⟨support, completion⟩ := Core.model_may_iff.mp ((observes translated).mpr evaluated)
  have exactResult : body.value.eval = .ok result := by simpa using completion.symm
  have stateSupported : body.start.supported .addition := support
  have starts : body.start? .addition = some body.start := by simp [Core.Body.start?, support]
  rw [Core.run, starts]
  change some ((Core.oracle .addition).run body.start fuel) = _
  rw [Core.run_exact stateSupported enough]
  change some (Bounded.stop (Core.State.finished body.value.eval)
    (.observed (.returned body.value.eval))) = _
  rw [exactResult]

end Silmaril.Proofs.Languages.Python.Compile.Closed

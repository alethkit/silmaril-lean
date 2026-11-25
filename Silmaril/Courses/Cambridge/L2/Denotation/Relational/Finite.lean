module

public import Silmaril.Courses.Cambridge.L2.Reduction
import Silmaril.Courses.Cambridge.L2.Denotation.Operational

/-! # Finite CBV evaluation with substitution

This presentation factors terminating paths into the way each source
construct evaluates its operands. It serves as the bridge from the original
small-step semantics to the environment interpretation.
-/

public section

namespace Silmaril.Courses.Cambridge.L2.RelationalDenotation

open Denotation (steps_under)

inductive SubstitutionReturn : Expr → Store → Config → Prop where
  | value {e : Expr} {s : Store} : IsValue e → SubstitutionReturn e s ⟨e, s⟩
  | add {left right : Expr} {s middle finish : Store} {a b : Int} :
      SubstitutionReturn left s ⟨.int a, middle⟩ →
      SubstitutionReturn right middle ⟨.int b, finish⟩ →
      SubstitutionReturn (.binary left .add right) s ⟨.int (a + b), finish⟩
  | ge {left right : Expr} {s middle finish : Store} {a b : Int} :
      SubstitutionReturn left s ⟨.int a, middle⟩ →
      SubstitutionReturn right middle ⟨.int b, finish⟩ →
      SubstitutionReturn (.binary left .ge right) s ⟨.bool (a ≥ b), finish⟩
  | deref {loc : Loc} {s : Store} {n : Int} :
      L1.Store.lookup s loc = some n → SubstitutionReturn (.deref loc) s ⟨.int n, s⟩
  | assign {loc : Loc} {rhs : Expr} {s finish : Store} {n : Int} :
      SubstitutionReturn rhs s ⟨.int n, finish⟩ → loc ∈ finish →
      SubstitutionReturn (.assign loc rhs) s ⟨.skip, finish.insert loc n⟩
  | seq {left right : Expr} {s middle : Store} {result : Config} :
      SubstitutionReturn left s ⟨.skip, middle⟩ → SubstitutionReturn right middle result →
      SubstitutionReturn (.seq left right) s result
  | ifTrue {test yes no : Expr} {s middle : Store} {result : Config} :
      SubstitutionReturn test s ⟨.bool true, middle⟩ → SubstitutionReturn yes middle result →
      SubstitutionReturn (.cond test yes no) s result
  | ifFalse {test yes no : Expr} {s middle : Store} {result : Config} :
      SubstitutionReturn test s ⟨.bool false, middle⟩ → SubstitutionReturn no middle result →
      SubstitutionReturn (.cond test yes no) s result
  | whileFalse {test body : Expr} {s finish : Store} :
      SubstitutionReturn test s ⟨.bool false, finish⟩ →
      SubstitutionReturn (.loop test body) s ⟨.skip, finish⟩
  | whileTrue {test body : Expr} {s afterTest afterBody finish : Store} :
      SubstitutionReturn test s ⟨.bool true, afterTest⟩ →
      SubstitutionReturn body afterTest ⟨.skip, afterBody⟩ →
      SubstitutionReturn (.loop test body) afterBody ⟨.skip, finish⟩ →
      SubstitutionReturn (.loop test body) s ⟨.skip, finish⟩
  | app {fn arg body argument : Expr} {A : Ty}
      {s afterFn afterArg : Store} {result : Config} :
      SubstitutionReturn fn s ⟨.lam A body, afterFn⟩ →
      SubstitutionReturn arg afterFn ⟨argument, afterArg⟩ →
      SubstitutionReturn (body.beta argument) afterArg result →
      SubstitutionReturn (.app fn arg) s result
  | letE {rhs body argument : Expr} {A : Ty} {s afterRhs : Store} {result : Config} :
      SubstitutionReturn rhs s ⟨argument, afterRhs⟩ →
      SubstitutionReturn (body.beta argument) afterRhs result →
      SubstitutionReturn (.letE A rhs body) s result
  | letRec {fn body : Expr} {A B : Ty} {s : Store} {result : Config} :
      SubstitutionReturn (body.beta (Expr.recClosure A B fn)) s result →
      SubstitutionReturn (.letRecFun A B fn body) s result

private theorem SubstitutionReturn.steps {e : Expr} {s : Store} {result : Config}
    (run : SubstitutionReturn e s result) : Steps ⟨e, s⟩ result ∧ IsValue result.expr := by
  induction run with
  | value value => exact ⟨.refl, value⟩
  | deref lookup => exact ⟨.single (.deref lookup), .int _⟩
  | @add _ rhs _ _ _ a _ _ _ left right =>
    have first := steps_under (fun e => .binary e .add rhs) (fun step => .binaryLeft step) left.1
    have second := steps_under (fun e => .binary (.int a) .add e) (fun step => .binaryRight (.int a) step) right.1
    exact ⟨(first.trans second).tail (.add _ _ _), .int _⟩
  | @ge _ rhs _ _ _ a _ _ _ left right =>
    have first := steps_under (fun e => .binary e .ge rhs) (fun step => .binaryLeft step) left.1
    have second := steps_under (fun e => .binary (.int a) .ge e) (fun step => .binaryRight (.int a) step) right.1
    exact ⟨(first.trans second).tail (.ge _ _ _), .bool _⟩
  | @assign loc _ _ _ _ _ present rhs =>
    have path := steps_under (Expr.assign loc) (fun step => .assignStep step) rhs.1
    exact ⟨path.tail (.assignValue present), .skip⟩
  | @seq _ rhs _ _ _ _ _ left right =>
    have path := steps_under (fun e => .seq e rhs) (fun step => .seqStep step) left.1
    exact ⟨(path.tail .seqSkip).trans right.1, right.2⟩
  | @ifTrue _ yesExpr noExpr _ _ _ _ _ test yes =>
    have path := steps_under (fun e => .cond e yesExpr noExpr) (fun step => .ifStep step) test.1
    exact ⟨(path.tail .ifTrue).trans yes.1, yes.2⟩
  | @ifFalse _ yesExpr noExpr _ _ _ _ _ test no =>
    have path := steps_under (fun e => .cond e yesExpr noExpr) (fun step => .ifStep step) test.1
    exact ⟨(path.tail .ifFalse).trans no.1, no.2⟩
  | @whileFalse testExpr bodyExpr _ _ _ test =>
    have path := steps_under (fun e => .cond e (.seq bodyExpr (.loop testExpr bodyExpr)) .skip)
      (fun step => .ifStep step) test.1
    exact ⟨.head .while (path.tail .ifFalse), .skip⟩
  | @whileTrue testExpr bodyExpr _ _ _ _ _ _ _ test body rest =>
    let loop := Expr.loop testExpr bodyExpr
    have guardPath := steps_under (fun e => .cond e (.seq bodyExpr loop) .skip)
      (fun step => .ifStep step) test.1
    have bodyPath := steps_under (fun e => .seq e loop) (fun step => .seqStep step) body.1
    have iteration := ((guardPath.tail .ifTrue).trans bodyPath).tail .seqSkip
    exact ⟨.head .while (iteration.trans rest.1), .skip⟩
  | @app _ arg body _ A _ _ _ _ _ _ _ fn actual returned =>
    have first := steps_under (fun e => .app e arg) (fun step => .appLeft step) fn.1
    have second := steps_under (Expr.app (.lam A body))
      (fun step => .appRight (.lam A body) step) actual.1
    exact ⟨((first.trans second).tail (.appFun actual.2)).trans returned.1, returned.2⟩
  | @letE _ body _ A _ _ _ _ _ rhs returned =>
    have first := steps_under (fun e => .letE A e body) (fun step => .letStep step) rhs.1
    exact ⟨(first.tail (.letValue rhs.2)).trans returned.1, returned.2⟩
  | letRec _ returned => exact ⟨.head .letRecFun returned.1, returned.2⟩

private theorem SubstitutionReturn.value_result {e : Expr} {s : Store} {result : Config}
    (value : IsValue e) (run : SubstitutionReturn e s result) : result = ⟨e, s⟩ := by
  cases value <;> cases run <;> rfl

private theorem SubstitutionReturn.before_step {before after result : Config} (step : Step before after)
    (run : SubstitutionReturn after.expr after.store result) :
    SubstitutionReturn before.expr before.store result := by
  induction step generalizing result with
  | add => cases run with | value => exact .add (.value (.int _)) (.value (.int _))
  | ge => cases run with | value => exact .ge (.value (.int _)) (.value (.int _))
  | binaryLeft _ ih =>
    cases run with
    | value value => cases value
    | add left right => exact .add (ih left) right
    | ge left right => exact .ge (ih left) right
  | binaryRight ready _ ih =>
    cases run with
    | value value => cases value
    | add left right =>
      cases left.value_result ready
      exact .add (.value ready) (ih right)
    | ge left right =>
      cases left.value_result ready
      exact .ge (.value ready) (ih right)
  | deref lookup => cases run with | value => exact .deref lookup
  | assignValue present => cases run with | value => exact .assign (.value (.int _)) present
  | assignStep _ ih =>
    cases run with
    | value value => cases value
    | assign rhs present => exact .assign (ih rhs) present
  | seqSkip => exact .seq (.value .skip) run
  | seqStep _ ih =>
    cases run with
    | value value => cases value
    | seq left right => exact .seq (ih left) right
  | ifTrue => exact .ifTrue (.value (.bool true)) run
  | ifFalse => exact .ifFalse (.value (.bool false)) run
  | ifStep _ ih =>
    cases run with
    | value value => cases value
    | ifTrue test yes => exact .ifTrue (ih test) yes
    | ifFalse test no => exact .ifFalse (ih test) no
  | «while» =>
    cases run with
    | value value => cases value
    | ifTrue test yes =>
      cases yes with
      | value value => cases value
      | seq body rest =>
        cases rest with
        | value value => cases value
        | whileFalse guard => exact .whileTrue test body (.whileFalse guard)
        | whileTrue guard next remaining => exact .whileTrue test body (.whileTrue guard next remaining)
    | ifFalse test no => cases no with | value => exact .whileFalse test
  | appLeft _ ih =>
    cases run with
    | value value => cases value
    | app fn arg body => exact .app (ih fn) arg body
  | appRight ready _ ih =>
    cases run with
    | value value => cases value
    | app fn arg body =>
      cases fn.value_result ready
      exact .app (.value ready) (ih arg) body
  | appFun ready => exact .app (.value (.lam _ _)) (.value ready) run
  | letStep _ ih =>
    cases run with
    | value value => cases value
    | letE rhs body => exact .letE (ih rhs) body
  | letValue ready => exact .letE (.value ready) run
  | letRecFun => exact .letRec run

private theorem SubstitutionReturn.of_steps {start result : Config}
    (path : Steps start result) (value : IsValue result.expr) :
    SubstitutionReturn start.expr start.store result := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => cases result; exact .value value
  | head step _ ih => exact SubstitutionReturn.before_step step ih

theorem substitutionReturn_iff {e : Expr} {s : Store} {result : Config} :
    SubstitutionReturn e s result ↔ Steps ⟨e, s⟩ result ∧ IsValue result.expr :=
  ⟨SubstitutionReturn.steps, fun ⟨steps, value⟩ => SubstitutionReturn.of_steps steps value⟩

end Silmaril.Courses.Cambridge.L2.RelationalDenotation

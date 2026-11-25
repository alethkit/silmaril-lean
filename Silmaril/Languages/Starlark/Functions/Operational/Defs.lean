module

public import Silmaril.Languages.Starlark.Functions.Expressions.Operational.Defs
public import Silmaril.Languages.Starlark.Functions.Builtins.Operational.Defs
public import Silmaril.Languages.Starlark.Lists.Iteration.Operational.Defs

public section

namespace Silmaril.Languages.Starlark.Functions

open Lists
open Lists.Iteration
  (Flow Suite Runs Cursor CursorRuns LoopTarget BindsTarget truth acquireIterator restoreIterators enterIterator)

mutual
/-- Big-step rules over the available declarations. The same declaration may
be invoked again after a call completes, but not while it is active. -/
inductive Exec (program : Program) : List DeclarationId → State → Body → Outcome Flow → Prop where
  | total {available : List DeclarationId} {s : State} {suite : Suite 0} {out : Outcome Flow} :
      Runs s (.suite suite) out → Exec program available s (.total suite) out
  | returnExpr {available : List DeclarationId} {s : State} {value : Lowering.Expr}
      {out : Outcome Lists.Value} :
      ExecExpr program available s value out →
      Exec program available s (.returnExpr value) (Outcome.resume out fun result => pure (.returned result))
  | assignExpr {available : List DeclarationId} {s : State} {target : Binding}
      {value : Lowering.Expr} {out : Outcome Lists.Value} :
      ExecExpr program available s value out →
      Exec program available s (.assignExpr target value)
        (Outcome.resume out fun result next => .ok .next (next.write target result))
  | assignTargetExpr {available : List DeclarationId} {s t : State} {target : LoopTarget}
      {rhs : Lowering.Expr} {value : Lists.Value} {out : Outcome Unit} :
      ExecExpr program available s rhs (.ok value t) → BindsTarget t value target out →
      Exec program available s (.assignTargetExpr target rhs) (Outcome.resume out fun () => pure .next)
  | assignTargetExprRhsError {available : List DeclarationId} {s t : State} {target : LoopTarget}
      {rhs : Lowering.Expr} {error : Error} :
      ExecExpr program available s rhs (.error error t) →
      Exec program available s (.assignTargetExpr target rhs) (.error error t)
  | assignScoped {available : List DeclarationId} {s : State} {target : Binding}
      {locals : List Binding} {body : Body} {out : Outcome Flow} :
      Exec program available (locals.foldl State.allocateSlot s) body out →
      Exec program available s (.assignScoped target locals body) (completeCall s (some target) out)
  | assignTargetScoped {available : List DeclarationId} {s t : State} {target : LoopTarget}
      {rhs : Body} {value : Lists.Value} {out : Outcome Unit} :
      Exec program available s rhs (.ok (.returned value) t) →
      BindsTarget (restoreCaller s t) value target out →
      Exec program available s (.assignTargetScoped target rhs) (Outcome.resume out fun () => pure .next)
  | assignTargetScopedError {available : List DeclarationId} {s t : State} {target : LoopTarget}
      {rhs : Body} {error : Error} :
      Exec program available s rhs (.error error t) →
      Exec program available s (.assignTargetScoped target rhs) (.error error (restoreCaller s t))
  | assignTargetScopedSignal {available : List DeclarationId} {s t : State} {target : LoopTarget}
      {rhs : Body} {signal : Flow} :
      Exec program available s rhs (.ok signal t) →
      (∀ value, signal ≠ .returned value) →
      Exec program available s (.assignTargetScoped target rhs) (.ok signal (restoreCaller s t))
  | setIndexExpr {available : List DeclarationId} {s t u : State}
      {receiver subscript rhs : Lowering.Expr} {value target : Lists.Value} {out : Outcome Lists.Value} :
      ExecExpr program available s rhs (.ok value t) →
      ExecExpr program available t receiver (.ok target u) →
      ExecExpr program available u subscript out →
      Exec program available s (.setIndexExpr receiver subscript rhs)
        (Outcome.resume out fun index next =>
          Outcome.resume (writeIndex target index value next) fun _ => pure .next)
  | setIndexExprReceiverError {available : List DeclarationId} {s t u : State}
      {receiver subscript rhs : Lowering.Expr} {value : Lists.Value} {error : Error} :
      ExecExpr program available s rhs (.ok value t) →
      ExecExpr program available t receiver (.error error u) →
      Exec program available s (.setIndexExpr receiver subscript rhs) (.error error u)
  | setIndexExprRhsError {available : List DeclarationId} {s t : State}
      {receiver subscript rhs : Lowering.Expr} {error : Error} :
      ExecExpr program available s rhs (.error error t) →
      Exec program available s (.setIndexExpr receiver subscript rhs) (.error error t)
  | addIndexExpr {available : List DeclarationId} {s t u v : State}
      {receiver subscript rhs : Lowering.Expr} {target index previous : Lists.Value} {out : Outcome Lists.Value} :
      ExecExpr program available s receiver (.ok target t) →
      ExecExpr program available t subscript (.ok index u) →
      readIndex target index u = .ok previous v →
      ExecExpr program available v rhs out →
      Exec program available s (.addIndexExpr receiver subscript rhs)
        (Outcome.resume out fun value next =>
          Outcome.resume (fromExcept (applyIntegerAdd previous value) next) fun sum next =>
            Outcome.resume (writeIndex target index sum next) fun _ => pure .next)
  | addIndexExprReadError {available : List DeclarationId} {s t u v : State}
      {receiver subscript rhs : Lowering.Expr} {target index : Lists.Value} {error : Error} :
      ExecExpr program available s receiver (.ok target t) →
      ExecExpr program available t subscript (.ok index u) →
      readIndex target index u = .error error v →
      Exec program available s (.addIndexExpr receiver subscript rhs) (.error error v)
  | addIndexExprSubscriptError {available : List DeclarationId} {s t u : State}
      {receiver subscript rhs : Lowering.Expr} {target : Lists.Value} {error : Error} :
      ExecExpr program available s receiver (.ok target t) →
      ExecExpr program available t subscript (.error error u) →
      Exec program available s (.addIndexExpr receiver subscript rhs) (.error error u)
  | addIndexExprReceiverError {available : List DeclarationId} {s t : State}
      {receiver subscript rhs : Lowering.Expr} {error : Error} :
      ExecExpr program available s receiver (.error error t) →
      Exec program available s (.addIndexExpr receiver subscript rhs) (.error error t)
  | assignIntegerAdd {available : List DeclarationId} {s : State} {target left right : Binding} :
      Exec program available s (.assignIntegerAdd target left right) (assignIntegerAdd target left right s)
  | evalExpr {available : List DeclarationId} {s : State} {value : Lowering.Expr}
      {out : Outcome Lists.Value} :
      ExecExpr program available s value out →
      Exec program available s (.evalExpr value) (Outcome.resume out fun _ => pure .next)
  | evalScoped {available : List DeclarationId} {s : State} {code : Body} {out : Outcome Flow} :
      Exec program available s code out →
      Exec program available s (.evalScoped code) (completeCall s none out)
  | insertDictEntry {available : List DeclarationId} {s : State} {receiver key value : Binding} :
      Exec program available s (.insertDictEntry receiver key value) (insertDictEntry receiver key value s)
  | seq {available : List DeclarationId} {s t : State} {first rest : Body} {out : Outcome Flow} :
      Exec program available s first (.ok .next t) → Exec program available t rest out →
      Exec program available s (.seq first rest) out
  | seqStop {available : List DeclarationId} {s t : State} {first rest : Body} {signal : Flow} :
      Exec program available s first (.ok signal t) → signal ≠ .next →
      Exec program available s (.seq first rest) (.ok signal t)
  | seqError {available : List DeclarationId} {s t : State} {first rest : Body} {error : Error} :
      Exec program available s first (.error error t) →
      Exec program available s (.seq first rest) (.error error t)
  | branch {available : List DeclarationId} {s t : State} {test : Lists.Expr} {yes no : Body}
      {value : Outcome Lists.Value} {flag : Bool} {out : Outcome Flow} :
      Eval s test value → Outcome.resume value truth = .ok flag t →
      Exec program available t (if flag then yes else no) out →
      Exec program available s (.branch test yes no) out
  | branchError {available : List DeclarationId} {s t : State} {test : Lists.Expr} {yes no : Body}
      {value : Outcome Lists.Value} {error : Error} :
      Eval s test value → Outcome.resume value truth = .error error t →
      Exec program available s (.branch test yes no) (.error error t)
  | branchExpr {available : List DeclarationId} {s t : State} {test : Lowering.Expr} {yes no : Body}
      {value : Outcome Lists.Value} {flag : Bool} {out : Outcome Flow} :
      ExecExpr program available s test value → Outcome.resume value truth = .ok flag t →
      Exec program available t (if flag then yes else no) out →
      Exec program available s (.branchExpr test yes no) out
  | branchExprError {available : List DeclarationId} {s t : State} {test : Lowering.Expr}
      {yes no : Body} {value : Outcome Lists.Value} {error : Error} :
      ExecExpr program available s test value → Outcome.resume value truth = .error error t →
      Exec program available s (.branchExpr test yes no) (.error error t)
  | forIn {available : List DeclarationId} {s t : State} {target : LoopTarget} {iterable : Lists.Expr}
      {body : Body} {value : Outcome Lists.Value} {guard : Option Address}
      {cursor : Cursor} {out : Outcome Flow} :
      Eval s iterable value → Outcome.resume value acquireIterator = .ok (guard, cursor) t →
      ExecCursor program available target body cursor (enterIterator t guard) out →
      Exec program available s (.forIn target iterable body) (restoreIterators t.iterators out)
  | forError {available : List DeclarationId} {s t : State} {target : LoopTarget}
      {iterable : Lists.Expr} {body : Body} {value : Outcome Lists.Value} {error : Error} :
      Eval s iterable value → Outcome.resume value acquireIterator = .error error t →
      Exec program available s (.forIn target iterable body) (.error error t)
  | forInExpr {available : List DeclarationId} {s t : State} {target : LoopTarget}
      {iterable : Lowering.Expr} {body : Body} {value : Outcome Lists.Value} {guard : Option Address}
      {cursor : Cursor} {out : Outcome Flow} :
      ExecExpr program available s iterable value → Outcome.resume value acquireIterator = .ok (guard, cursor) t →
      ExecCursor program available target body cursor (enterIterator t guard) out →
      Exec program available s (.forInExpr target iterable body) (restoreIterators t.iterators out)
  | forInExprError {available : List DeclarationId} {s t : State} {target : LoopTarget}
      {iterable : Lowering.Expr} {body : Body} {value : Outcome Lists.Value} {error : Error} :
      ExecExpr program available s iterable value → Outcome.resume value acquireIterator = .error error t →
      Exec program available s (.forInExpr target iterable body) (.error error t)
  | breakLoop {available : List DeclarationId} {s : State} :
      Exec program available s .breakLoop (.ok .breakLoop s)
  | continueLoop {available : List DeclarationId} {s : State} :
      Exec program available s .continueLoop (.ok .continueLoop s)
  | define {available : List DeclarationId} {s : State} {target : Binding} {id : DeclarationId}
      {defaults : Outcome (List Lists.Value)} :
      ExecExprs program available s (defaultOperands program id) defaults →
      Exec program available s (.define target id) (Outcome.resume defaults (define program target id))
  | call {available : List DeclarationId} {s t : State} {target : Option Binding}
      {callee : Lists.Expr} {arguments : Arguments} {operands : Outcome (List Lists.Value)}
      {plan : Prepared available} {out : Outcome Flow} :
      Eval s (Arguments.operands callee arguments) operands →
      Outcome.resume operands (prepare program available arguments) = .ok (.closure plan) t →
      Exec program (withoutDeclaration available plan.id) t plan.body out →
      Exec program available s (.call target callee arguments) (completeCall s target out)
  | callBuiltin {available : List DeclarationId} {s t : State} {target : Option Binding}
      {callee : Lists.Expr} {arguments : Arguments} {operands : Outcome (List Lists.Value)}
      {id : Builtin} {actual : Actual} {out : Outcome Lists.Value} :
      Eval s (Arguments.operands callee arguments) operands →
      Outcome.resume operands (prepare program available arguments) = .ok (.builtin id actual) t →
      Builtins.Invokes t id actual out →
      Exec program available s (.call target callee arguments)
        (Outcome.resume out (writeCallResult target))
  | callError {available : List DeclarationId} {s t : State} {target : Option Binding}
      {callee : Lists.Expr} {arguments : Arguments} {operands : Outcome (List Lists.Value)}
      {error : Error} :
      Eval s (Arguments.operands callee arguments) operands →
      Outcome.resume operands (prepare program available arguments) = .error error t →
      Exec program available s (.call target callee arguments) (.error error t)

/-- Cursor bodies execute under the caller's available declaration set. -/
inductive ExecCursor (program : Program) :
    List DeclarationId → LoopTarget → Body → Cursor → State → Outcome Flow → Prop where
  | runs {available : List DeclarationId} {target : LoopTarget} {body : Body} {cursor : Cursor}
      {s : State} {out : Outcome Flow} {bodyRuns : State → Outcome Flow → Prop} :
      (∀ state result, bodyRuns state result → Exec program available state body result) →
      CursorRuns bodyRuns target cursor s out → ExecCursor program available target body cursor s out

/-- Expression operands in a body use the expression rules with closure
executions discharged under their reduced declaration sets. -/
inductive ExecExpr (program : Program) :
    List DeclarationId → State → Lowering.Expr → Outcome Lists.Value → Prop where
  | evaluates {available : List DeclarationId} {s : State} {expression : Lowering.Expr}
      {out : Outcome Lists.Value} {calls : Lowering.ClosureRuns available} :
      (∀ plan next result, calls plan next result →
        Exec program (withoutDeclaration available plan.id) next plan.body result) →
      Lowering.EvaluatesWith program available calls (fun _ => True) s expression out →
      ExecExpr program available s expression out

/-- A sequence of operands in one frame, with closure premises discharged
under their reduced declaration sets. -/
inductive ExecExprs (program : Program) :
    List DeclarationId → State → List Lowering.Expr → Outcome (List Lists.Value) → Prop where
  | evaluatesMany {available : List DeclarationId} {s : State} {expressions : List Lowering.Expr}
      {out : Outcome (List Lists.Value)} {calls : Lowering.ClosureRuns available} :
      (∀ plan next result, calls plan next result →
        Exec program (withoutDeclaration available plan.id) next plan.body result) →
      Lowering.EvaluatesManyWith program available calls (fun _ => True) s expressions out →
      ExecExprs program available s expressions out
end

abbrev ExecItems (program : Program) (available : List DeclarationId) (target : Binding)
    (body : Body) (items : List Lists.Value) : State → Outcome Flow → Prop :=
  ExecCursor program available target body (.items items)

end Silmaril.Languages.Starlark.Functions

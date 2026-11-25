module

public import Silmaril.Languages.Starlark.Functions.Expressions.Operational.Defs
public import Silmaril.Languages.Starlark.Functions.Builtins.Operational.Defs
public import Silmaril.Languages.Starlark.Lists.Iteration.Operational.Defs

public section

namespace Silmaril.Languages.Starlark.Functions

open Lists
open Lists.Iteration (Flow Suite Runs truth iterationSource restoreIterators pushIterator)

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
  | evalExpr {available : List DeclarationId} {s : State} {value : Lowering.Expr}
      {out : Outcome Lists.Value} :
      ExecExpr program available s value out →
      Exec program available s (.evalExpr value) (Outcome.resume out fun _ => pure .next)
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
  | forIn {available : List DeclarationId} {s t : State} {target : Binding} {iterable : Lists.Expr}
      {body : Body} {value : Outcome Lists.Value} {address : Address}
      {items : List Lists.Value} {out : Outcome Flow} :
      Eval s iterable value → Outcome.resume value iterationSource = .ok (address, items) t →
      ExecItems program available target body items (pushIterator t address) out →
      Exec program available s (.forIn target iterable body) (restoreIterators t.iterators out)
  | forError {available : List DeclarationId} {s t : State} {target : Binding}
      {iterable : Lists.Expr} {body : Body} {value : Outcome Lists.Value} {error : Error} :
      Eval s iterable value → Outcome.resume value iterationSource = .error error t →
      Exec program available s (.forIn target iterable body) (.error error t)
  | forInExpr {available : List DeclarationId} {s t : State} {target : Binding}
      {iterable : Lowering.Expr} {body : Body} {value : Outcome Lists.Value} {address : Address}
      {items : List Lists.Value} {out : Outcome Flow} :
      ExecExpr program available s iterable value → Outcome.resume value iterationSource = .ok (address, items) t →
      ExecItems program available target body items (pushIterator t address) out →
      Exec program available s (.forInExpr target iterable body) (restoreIterators t.iterators out)
  | forInExprError {available : List DeclarationId} {s t : State} {target : Binding}
      {iterable : Lowering.Expr} {body : Body} {value : Outcome Lists.Value} {error : Error} :
      ExecExpr program available s iterable value → Outcome.resume value iterationSource = .error error t →
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

/-- Iteration keeps the caller's guard in force while an item executes its body. -/
inductive ExecItems (program : Program) :
    List DeclarationId → Binding → Body → List Lists.Value → State → Outcome Flow → Prop where
  | done {available : List DeclarationId} {target : Binding} {body : Body} {s : State} :
      ExecItems program available target body [] s (.ok .next s)
  | next {available : List DeclarationId} {target : Binding} {body : Body} {s t : State}
      {value : Lists.Value} {rest : List Lists.Value} {out : Outcome Flow} :
      Exec program available (s.write target value) body (.ok .next t) →
      ExecItems program available target body rest t out →
      ExecItems program available target body (value :: rest) s out
  | continueLoop {available : List DeclarationId} {target : Binding} {body : Body} {s t : State}
      {value : Lists.Value} {rest : List Lists.Value} {out : Outcome Flow} :
      Exec program available (s.write target value) body (.ok .continueLoop t) →
      ExecItems program available target body rest t out →
      ExecItems program available target body (value :: rest) s out
  | breakLoop {available : List DeclarationId} {target : Binding} {body : Body} {s t : State}
      {value : Lists.Value} {rest : List Lists.Value} :
      Exec program available (s.write target value) body (.ok .breakLoop t) →
      ExecItems program available target body (value :: rest) s (.ok .next t)
  | returned {available : List DeclarationId} {target : Binding} {body : Body} {s t : State}
      {value result : Lists.Value} {rest : List Lists.Value} :
      Exec program available (s.write target value) body (.ok (.returned result) t) →
      ExecItems program available target body (value :: rest) s (.ok (.returned result) t)
  | failed {available : List DeclarationId} {target : Binding} {body : Body} {s t : State}
      {value : Lists.Value} {rest : List Lists.Value} {error : Error} :
      Exec program available (s.write target value) body (.error error t) →
      ExecItems program available target body (value :: rest) s (.error error t)

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

end Silmaril.Languages.Starlark.Functions

module

public import Silmaril.Languages.Starlark.Functions.Defs
public import Silmaril.Languages.Starlark.Functions.Builtins.Operational.Defs
public import Silmaril.Languages.Starlark.Lists.Operational.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (State Outcome)
open Lists.Iteration (Flow truth)

/-- The closure premises are indexed by the prepared declaration and its
permission to call from the current declaration set. -/
abbrev ClosureRuns (available : List DeclarationId) :=
  Prepared available → State → Outcome Flow → Prop

/-- Expansion runs only after all operands have evaluated. The pinned
profile checks the mapping before the iterable. -/
inductive Expands (args : EvaluatedArguments) (state : State) : Outcome Actual → Prop where
  | mappingError {error : Lists.Error} {next : State} :
      expandStarStar args.starStar state = .error error next →
      Expands args state (.error error next)
  | spreadError {keys : List (String × Lists.Value)} {next final : State} {error : Lists.Error} :
      expandStarStar args.starStar state = .ok keys next →
      expandStar args.star next = .error error final →
      Expands args state (.error error final)
  | success {keys : List (String × Lists.Value)} {values : List Lists.Value} {next final : State} :
      expandStarStar args.starStar state = .ok keys next →
      expandStar args.star next = .ok values final →
      Expands args state (.ok ⟨args.positional ++ values, args.keywords ++ keys⟩ final)

/-- Dispatch shares value-level call preparation, including argument binding,
and delegates callee bodies to the supplied closure judgment. -/
inductive DispatchesWith (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available)
    (state : State) (callee : Lists.Value) (actual : Actual) : Outcome Lists.Value → Prop where
  | reject {error : Lists.Error} {next : State} :
      prepareExpanded program available actual callee state = .error error next →
      DispatchesWith program available calls state callee actual (.error error next)
  | builtin {id : Lists.Builtin} {bound : Actual} {next : State} {out : Outcome Lists.Value} :
      prepareExpanded program available actual callee state = .ok (.builtin id bound) next →
      Builtins.Invokes next id bound out →
      DispatchesWith program available calls state callee actual out
  | returned {plan : Prepared available} {next final : State} {flow : Flow} :
      prepareExpanded program available actual callee state = .ok (.closure plan) next →
      calls plan next (.ok flow final) →
      DispatchesWith program available calls state callee actual (.ok (callValue flow) (restoreCaller state final))
  | failed {plan : Prepared available} {next final : State} {error : Lists.Error} :
      prepareExpanded program available actual callee state = .ok (.closure plan) next →
      calls plan next (.error error final) →
      DispatchesWith program available calls state callee actual (.error error (restoreCaller state final))

inductive AppliesWith (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available) (shape : ArgumentShape)
    (state : State) : List Lists.Value → Outcome Lists.Value → Prop where
  | expansionError {callee : Lists.Value} {operands : List Lists.Value}
      {error : Lists.Error} {next : State} :
      Expands (shape.collect operands) state (.error error next) →
      AppliesWith program available calls shape state (callee :: operands) (.error error next)
  | expanded {callee : Lists.Value} {operands : List Lists.Value}
      {actual : Actual} {next : State} {out : Outcome Lists.Value} :
      Expands (shape.collect operands) state (.ok actual next) →
      DispatchesWith program available calls next callee actual out →
      AppliesWith program available calls shape state (callee :: operands) out

/-- In resolved calls, keyword expressions follow the positional expressions.
The optional iterable and mapping expressions follow in that order. -/
def sourceOperands (callee : Expr) (positional : List Expr) (keywords : List (String × Expr))
    (star starStar : Option Expr) : List Expr :=
  callee :: (positional ++ keywords.map Prod.snd ++ star.toList ++ starStar.toList)

/-- All atoms satisfy the supplied policy, including those on skipped paths.
The call syntax and lexical context are assumed to have been resolved. -/
inductive AdmittedWith (atomAllowed : Lists.Expr → Prop) : Expr → Prop where
  | atom {expression : Lists.Expr} : atomAllowed expression → AdmittedWith atomAllowed (.atom expression)
  | call {callee : Expr} {positional : List Expr} {keywords : List (String × Expr)}
      {star starStar : Option Expr} :
      (∀ operand ∈ sourceOperands callee positional keywords star starStar, AdmittedWith atomAllowed operand) →
      AdmittedWith atomAllowed (.call callee positional keywords star starStar)
  | branch {test yes no : Expr} :
      AdmittedWith atomAllowed test → AdmittedWith atomAllowed yes → AdmittedWith atomAllowed no → AdmittedWith atomAllowed (.branch test yes no)
  | logical {op : LogicalOp} {left right : Expr} :
      AdmittedWith atomAllowed left → AdmittedWith atomAllowed right → AdmittedWith atomAllowed (.logical op left right)

mutual
/-- Source rules evaluate operands left to right and stop at the first
error. A short-circuit returns the selected operand value. -/
inductive EvaluatesWith (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available) (atomAllowed : Lists.Expr → Prop) :
    State → Expr → Outcome Lists.Value → Prop where
  | atom {s : State} {expression : Lists.Expr} {out : Outcome Lists.Value} :
      atomAllowed expression → Lists.Eval s expression out →
      EvaluatesWith program available calls atomAllowed s (.atom expression) out
  | call {s t : State} {callee : Expr} {positional : List Expr} {keywords : List (String × Expr)}
      {star starStar : Option Expr} {values : List Lists.Value} {out : Outcome Lists.Value} :
      EvaluatesManyWith program available calls atomAllowed s (sourceOperands callee positional keywords star starStar)
        (.ok values t) →
      AppliesWith program available calls (argumentShape positional keywords star starStar) t values out →
      EvaluatesWith program available calls atomAllowed s (.call callee positional keywords star starStar) out
  | callError {s t : State} {callee : Expr} {positional : List Expr} {keywords : List (String × Expr)}
      {star starStar : Option Expr} {error : Lists.Error} :
      EvaluatesManyWith program available calls atomAllowed s (sourceOperands callee positional keywords star starStar)
        (.error error t) →
      EvaluatesWith program available calls atomAllowed s (.call callee positional keywords star starStar) (.error error t)
  | branch {s t : State} {test yes no : Expr} {tested out : Outcome Lists.Value} {flag : Bool} :
      EvaluatesWith program available calls atomAllowed s test tested →
      Outcome.resume tested truth = .ok flag t →
      EvaluatesWith program available calls atomAllowed t (if flag then yes else no) out →
      EvaluatesWith program available calls atomAllowed s (.branch test yes no) out
  | branchError {s t : State} {test yes no : Expr} {tested : Outcome Lists.Value} {error : Lists.Error} :
      EvaluatesWith program available calls atomAllowed s test tested →
      Outcome.resume tested truth = .error error t →
      EvaluatesWith program available calls atomAllowed s (.branch test yes no) (.error error t)
  | logical {s t : State} {op : LogicalOp} {left right : Expr} {value : Lists.Value}
      {flag : Bool} {out : Outcome Lists.Value} :
      EvaluatesWith program available calls atomAllowed s left (.ok value t) →
      truth value t = .ok flag t →
      (if op = .and then flag else !flag) = true →
      EvaluatesWith program available calls atomAllowed t right out →
      EvaluatesWith program available calls atomAllowed s (.logical op left right) out
  | shortCircuit {s t : State} {op : LogicalOp} {left right : Expr} {value : Lists.Value} {flag : Bool} :
      EvaluatesWith program available calls atomAllowed s left (.ok value t) →
      truth value t = .ok flag t →
      (if op = .and then flag else !flag) = false →
      EvaluatesWith program available calls atomAllowed s (.logical op left right) (.ok value t)
  | logicalError {s t : State} {op : LogicalOp} {left right : Expr}
      {tested : Outcome Lists.Value} {error : Lists.Error} :
      EvaluatesWith program available calls atomAllowed s left tested →
      Outcome.resume tested truth = .error error t →
      EvaluatesWith program available calls atomAllowed s (.logical op left right) (.error error t)

inductive EvaluatesManyWith (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available) (atomAllowed : Lists.Expr → Prop) :
    State → List Expr → Outcome (List Lists.Value) → Prop where
  | empty {s : State} : EvaluatesManyWith program available calls atomAllowed s [] (.ok [] s)
  | cons {s t u : State} {head : Expr} {tail : List Expr} {value : Lists.Value}
      {values : List Lists.Value} :
      EvaluatesWith program available calls atomAllowed s head (.ok value t) →
      EvaluatesManyWith program available calls atomAllowed t tail (.ok values u) →
      EvaluatesManyWith program available calls atomAllowed s (head :: tail) (.ok (value :: values) u)
  | headError {s t : State} {head : Expr} {tail : List Expr} {error : Lists.Error} :
      EvaluatesWith program available calls atomAllowed s head (.error error t) →
      EvaluatesManyWith program available calls atomAllowed s (head :: tail) (.error error t)
  | tailError {s t u : State} {head : Expr} {tail : List Expr} {value : Lists.Value}
      {error : Lists.Error} :
      EvaluatesWith program available calls atomAllowed s head (.ok value t) →
      EvaluatesManyWith program available calls atomAllowed t tail (.error error u) →
      EvaluatesManyWith program available calls atomAllowed s (head :: tail) (.error error u)
end

end Silmaril.Languages.Starlark.Functions.Lowering

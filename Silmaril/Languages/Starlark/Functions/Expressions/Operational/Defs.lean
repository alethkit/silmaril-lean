module

public import Silmaril.Languages.Starlark.Functions.Defs
public import Silmaril.Languages.Starlark.Functions.Builtins.Operational.Defs
public import Silmaril.Languages.Starlark.Lists.Operational.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (State Outcome Address Entry RangeValue listElements tupleElements dictEntries)
open Lists.Iteration (Cursor CursorCollects Flow truth)

/-- The closure premises are indexed by the prepared declaration and its
permission to call from the current declaration set. -/
abbrev ClosureRuns (available : List DeclarationId) :=
  Prepared available → State → Outcome Flow → Prop

/-- Positional spreading reads ordered elements without allocating a language value. -/
inductive ExpandsStar (state : State) : Option Lists.Value → Outcome (List Lists.Value) → Prop where
  | empty : ExpandsStar state none (.ok [] state)
  | list (address : Address) : ExpandsStar state (some (.list address)) (listElements address state)
  | tuple (address : Address) : ExpandsStar state (some (.tuple address)) (tupleElements address state)
  | dict (address : Address) : ExpandsStar state (some (.dict address))
      (Outcome.resume (dictEntries address state) fun entries => pure (entries.map Entry.key))
  | range {span : RangeValue} {values : List Lists.Value} :
      CursorCollects (Cursor.ofRange span) values → ExpandsStar state (some (.range span)) (.ok values state)
  | invalid {value : Lists.Value} : ¬ Builtins.IsCollection value →
      ExpandsStar state (some value) (.error .invalidStar state)

/-- Expansion runs only after all operands have evaluated. The pinned
profile checks the mapping before the iterable. -/
inductive Expands (args : EvaluatedArguments) (state : State) : Outcome Actual → Prop where
  | mappingError {error : Lists.Error} {next : State} :
      expandStarStar args.starStar state = .error error next →
      Expands args state (.error error next)
  | spreadError {keys : List (String × Lists.Value)} {next final : State} {error : Lists.Error} :
      expandStarStar args.starStar state = .ok keys next →
      ExpandsStar next args.star (.error error final) →
      Expands args state (.error error final)
  | success {keys : List (String × Lists.Value)} {values : List Lists.Value} {next final : State} :
      expandStarStar args.starStar state = .ok keys next →
      ExpandsStar next args.star (.ok values final) →
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
  | list {elements : List Expr} :
      (∀ element ∈ elements, AdmittedWith atomAllowed element) → AdmittedWith atomAllowed (.list elements)
  | tuple {elements : List Expr} :
      (∀ element ∈ elements, AdmittedWith atomAllowed element) → AdmittedWith atomAllowed (.tuple elements)
  | dict {entries : List (Expr × Expr)} :
      (∀ entry ∈ entries, AdmittedWith atomAllowed entry.1) →
      (∀ entry ∈ entries, AdmittedWith atomAllowed entry.2) → AdmittedWith atomAllowed (.dict entries)
  | index {receiver subscript : Expr} :
      AdmittedWith atomAllowed receiver → AdmittedWith atomAllowed subscript →
      AdmittedWith atomAllowed (.index receiver subscript)
  | slice {receiver start stop stride : Expr} :
      (∀ operand ∈ [receiver, start, stop, stride], AdmittedWith atomAllowed operand) →
      AdmittedWith atomAllowed (.slice receiver start stop stride)
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
  | list {s : State} {elements : List Expr} {out : Outcome (List Lists.Value)} :
      EvaluatesManyWith program available calls atomAllowed s elements out →
      EvaluatesWith program available calls atomAllowed s (.list elements) (Outcome.resume out Lists.allocate)
  | tuple {s : State} {elements : List Expr} {out : Outcome (List Lists.Value)} :
      EvaluatesManyWith program available calls atomAllowed s elements out →
      EvaluatesWith program available calls atomAllowed s (.tuple elements) (Outcome.resume out Lists.allocateTuple)
  | dict {s t : State} {entries : List (Expr × Expr)} {receiver : Lists.Value} {out : Outcome Unit} :
      Lists.allocateDict [] s = .ok receiver t →
      EvaluatesEntriesWith program available calls atomAllowed receiver t entries out →
      EvaluatesWith program available calls atomAllowed s (.dict entries) (Outcome.resume out fun _ => pure receiver)
  | index {s t : State} {receiver subscript : Expr} {value : Lists.Value} {out : Outcome Lists.Value} :
      EvaluatesWith program available calls atomAllowed s receiver (.ok value t) →
      EvaluatesWith program available calls atomAllowed t subscript out →
      EvaluatesWith program available calls atomAllowed s (.index receiver subscript)
        (Outcome.resume out (Lists.readIndex value))
  | indexReceiverError {s t : State} {receiver subscript : Expr} {error : Lists.Error} :
      EvaluatesWith program available calls atomAllowed s receiver (.error error t) →
      EvaluatesWith program available calls atomAllowed s (.index receiver subscript) (.error error t)
  | slice {s : State} {receiver start stop stride : Expr} {out : Outcome (List Lists.Value)} :
      EvaluatesManyWith program available calls atomAllowed s [receiver, start, stop, stride] out →
      EvaluatesWith program available calls atomAllowed s (.slice receiver start stop stride)
        (Outcome.resume out Lists.readSliceOperands)
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

/-- Evaluate one key and value, commit the checked pair, and then continue. -/
inductive EvaluatesEntriesWith (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available) (atomAllowed : Lists.Expr → Prop) :
    Lists.Value → State → List (Expr × Expr) → Outcome Unit → Prop where
  | noEntries {receiver : Lists.Value} {s : State} :
      EvaluatesEntriesWith program available calls atomAllowed receiver s [] (.ok () s)
  | keyError {receiver : Lists.Value} {s t : State} {key value : Expr}
      {rest : List (Expr × Expr)} {error : Lists.Error} :
      EvaluatesWith program available calls atomAllowed s key (.error error t) →
      EvaluatesEntriesWith program available calls atomAllowed receiver s ((key, value) :: rest) (.error error t)
  | valueError {receiver k : Lists.Value} {s t u : State} {key value : Expr}
      {rest : List (Expr × Expr)} {error : Lists.Error} :
      EvaluatesWith program available calls atomAllowed s key (.ok k t) →
      EvaluatesWith program available calls atomAllowed t value (.error error u) →
      EvaluatesEntriesWith program available calls atomAllowed receiver s ((key, value) :: rest) (.error error u)
  | insertionError {receiver k v : Lists.Value} {s t u w : State} {key value : Expr}
      {rest : List (Expr × Expr)} {error : Lists.Error} :
      EvaluatesWith program available calls atomAllowed s key (.ok k t) →
      EvaluatesWith program available calls atomAllowed t value (.ok v u) →
      Lists.insertDisplayEntry receiver k v u = .error error w →
      EvaluatesEntriesWith program available calls atomAllowed receiver s ((key, value) :: rest) (.error error w)
  | entry {receiver k v : Lists.Value} {s t u w : State} {key value : Expr}
      {rest : List (Expr × Expr)} {out : Outcome Unit} :
      EvaluatesWith program available calls atomAllowed s key (.ok k t) →
      EvaluatesWith program available calls atomAllowed t value (.ok v u) →
      Lists.insertDisplayEntry receiver k v u = .ok () w →
      EvaluatesEntriesWith program available calls atomAllowed receiver w rest out →
      EvaluatesEntriesWith program available calls atomAllowed receiver s ((key, value) :: rest) out
end

end Silmaril.Languages.Starlark.Functions.Lowering

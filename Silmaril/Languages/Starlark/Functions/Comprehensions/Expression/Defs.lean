module

public import Silmaril.Languages.Starlark.Functions.Comprehensions.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Comprehensions

/-- Comprehensions in the checked return and name-assignment profile.
The existing expression grammar supplies ordinary leaves and call callees. -/
inductive Expression where
  | plain (value : Lowering.Expr)
  | list (comp : ListComp)
  | dict (comp : DictComp)
  | callPos (callee : Lowering.Expr) (arguments : List Expression)
  | branch (test yes no : Expression)
  | logical (op : LogicalOp) (left right : Expression)

def expressionSlot : Binding := ⟨.global, "$comp-expression"⟩

def argumentSlot (index : Nat) : Binding := ⟨.global, "$comp-argument" ++ toString index⟩

def readSaved (name : Binding) : Lists.Expr := .read (.bound name)

def returnSaved (name : Binding) : Body := .returnExpr (.atom (readSaved name))

/-- Evaluate each operand into its own saved binding before entering dispatch.
The containing call scope restores these bindings on both exits. -/
def stageArguments (index : Nat) (arguments : List (Binding → Body))
    (dispatch : List Lists.Expr → Body) : Body :=
  match arguments with
  | [] => dispatch []
  | argument :: rest =>
    .seq (argument (argumentSlot index))
      (stageArguments (index + 1) rest fun saved => dispatch (readSaved (argumentSlot index) :: saved))

/-- Choose direct operands or reuse the existing scratch lowerers, without
changing the expression site at which any operand runs. -/
structure ExpressionStages where
  plain : Stage
  list : ListComp → Binding → Body
  dict : DictComp → Binding → Body

def directStages : ExpressionStages :=
  ⟨Body.assignExpr, ListComp.body, DictComp.body⟩

def loweredStages (start : Nat) : ExpressionStages :=
  ⟨stageLowered start, fun comp target => comp.lower target start, fun comp target => comp.lower target start⟩

def Expression.compile (stages : ExpressionStages) (expr : Expression) (target : Binding) : Body :=
  match expr with
  | .plain value => stages.plain target value
  | .list comp => stages.list comp target
  | .dict comp => stages.dict comp target
  | .callPos callee arguments =>
    let operands := arguments.attach.map fun arg =>
      have := List.sizeOf_lt_of_mem arg.property
      arg.val.compile stages
    .assignScoped target [] (.seq (stages.plain (argumentSlot 0) callee)
      (stageArguments 1 operands fun saved =>
        .seq (.call (some expressionSlot) (readSaved (argumentSlot 0)) { positional := saved })
          (returnSaved expressionSlot)))
  | .branch test yes no =>
    .assignScoped target [] (.seq (test.compile stages expressionSlot)
      (.branch (readSaved expressionSlot)
        (.seq (yes.compile stages expressionSlot) (returnSaved expressionSlot))
        (.seq (no.compile stages expressionSlot) (returnSaved expressionSlot))))
  | .logical op left right =>
    let takeRight := Body.seq (right.compile stages expressionSlot) (returnSaved expressionSlot)
    let keepLeft := returnSaved expressionSlot
    let next := match op with
      | .and => Body.branch (readSaved expressionSlot) takeRight keepLeft
      | .or => Body.branch (readSaved expressionSlot) keepLeft takeRight
    .assignScoped target [] (.seq (left.compile stages expressionSlot) next)
termination_by sizeOf expr
decreasing_by all_goals first | assumption | (simp_wf; omega)

def Expression.body (expr : Expression) (target : Binding) : Body :=
  expr.compile directStages target

def Expression.lower (expr : Expression) (target : Binding) (start : Nat := 0) : Body :=
  expr.compile (loweredStages start) target

/-- Pass the staged value to the ordinary return transition. The enclosing
call restores its caller frame, including any private return binding. -/
def Expression.returnCode (expr : Expression) (stages : ExpressionStages) : Body :=
  .seq (expr.compile stages expressionSlot) (returnSaved expressionSlot)

end Silmaril.Languages.Starlark.Functions.Comprehensions

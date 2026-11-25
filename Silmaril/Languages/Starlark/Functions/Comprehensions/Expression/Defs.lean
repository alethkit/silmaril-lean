module

public import Silmaril.Languages.Starlark.Functions.Comprehensions.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Comprehensions

/-- Comprehensions in the checked return and name-assignment profile.
The existing expression grammar supplies ordinary leaves. -/
inductive Expression where
  | plain (value : Lowering.Expr)
  | list (comp : ListComp)
  | dict (comp : DictComp)
  | listDisplay (elements : List Expression)
  | tupleDisplay (elements : List Expression)
  | dictDisplay (entries : List (Expression × Expression))
  | index (receiver subscript : Expression)
  | callPos (callee : Lowering.Expr) (arguments : List Expression)
  /-- Positional operands, then named operands, then at most one of each spread. -/
  | call (callee : Expression) (positional : List Expression)
      (keywords : List (String × Expression)) (star starStar : Option Expression)
  | branch (test yes no : Expression)
  | logical (op : LogicalOp) (left right : Expression)

theorem callOperandSize (callee : Expression) (positional : List Expression)
    (keywords : List (String × Expression)) (star starStar : Option Expression) {part : Expression}
    (member : part ∈ Lowering.argumentExprs positional keywords star starStar) :
    sizeOf part < sizeOf (.call callee positional keywords star starStar : Expression) := by
  simp only [Lowering.argumentExprs, List.mem_append] at member
  rcases member with ((pos | named) | spread) | mapping
  · have := List.sizeOf_lt_of_mem pos
    simp
    omega
  · obtain ⟨⟨name, value⟩, inKeywords, rfl⟩ := List.mem_map.mp named
    have := List.sizeOf_lt_of_mem inKeywords
    simp at this ⊢
    omega
  · obtain rfl := Option.mem_toList.mp spread
    simp
    omega
  · obtain rfl := Option.mem_toList.mp mapping
    simp
    omega

def expressionSlot : Binding := ⟨.global, "$comp-expression"⟩

def argumentSlot (index : Nat) : Binding := ⟨.global, "$comp-argument" ++ toString index⟩

def readSaved (name : Binding) : Lists.Expr := .read (.bound name)

def returnSaved (name : Binding) : Body := .returnExpr (.atom (readSaved name))

/-- Evaluate each operand into its own saved binding before the final operation.
The containing expression scope restores these bindings on both exits. -/
def stageArguments (index : Nat) (arguments : List (Binding → Body))
    (dispatch : List Lists.Expr → Body) : Body :=
  match arguments with
  | [] => dispatch []
  | argument :: rest =>
    .seq (argument (argumentSlot index))
      (stageArguments (index + 1) rest fun saved => dispatch (readSaved (argumentSlot index) :: saved))

/-- Lists and tuples allocate only after every element has succeeded. -/
def compileSequence (target : Binding) (finish : List Lists.Expr → Lists.Expr)
    (elements : List (Binding → Body)) : Body :=
  .assignScoped target [] (stageArguments 0 elements fun saved => .returnExpr (.atom (finish saved)))

/-- Stage the key and then the value before inserting one pair. -/
def stageDisplayEntry (key value : Binding → Body) (rest : Body) : Body :=
  .seq (key (argumentSlot 0)) (.seq (value (argumentSlot 1))
    (.seq (.insertDictEntry expressionSlot (argumentSlot 0) (argumentSlot 1)) rest))

/-- Allocate before the first pair, then validate each pair before starting the next. -/
def compileDictDisplay (target : Binding) (entries : List ((Binding → Body) × (Binding → Body))) : Body :=
  .assignScoped target [] (.seq (.assignExpr expressionSlot (.atom (.dict .noEntries)))
    (entries.foldr (fun (key, value) rest => stageDisplayEntry key value rest) (returnSaved expressionSlot)))

/-- Select the existing indexing primitive only after the receiver and index have run. -/
def compileIndex (target : Binding) (receiver subscript : Binding → Body) : Body :=
  .assignScoped target [] (.seq (receiver (argumentSlot 0)) (.seq (subscript (argumentSlot 1))
    (.returnExpr (.atom (.index (readSaved (argumentSlot 0)) (readSaved (argumentSlot 1)))))))

/-- Only the final body operation expands arguments or prepares a call.
Its operands read the saved values using the regular argument shape. -/
def compileCall (target : Binding) (callee : Body) (shape : ArgumentShape)
    (operands : List (Binding → Body)) : Body :=
  .assignScoped target [] (.seq callee
    (stageArguments 1 operands fun saved =>
      .seq (.call (some expressionSlot) (readSaved (argumentSlot 0)) (Lowering.fillArguments shape saved))
        (returnSaved expressionSlot)))

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
  | .listDisplay elements =>
    compileSequence target (.list ∘ operandList) (elements.attach.map fun element =>
      have := List.sizeOf_lt_of_mem element.property
      element.val.compile stages)
  | .tupleDisplay elements =>
    compileSequence target (.tuple ∘ operandList) (elements.attach.map fun element =>
      have := List.sizeOf_lt_of_mem element.property
      element.val.compile stages)
  | .dictDisplay entries =>
    compileDictDisplay target (entries.attach.map fun ⟨(key, value), member⟩ =>
      have := (Lowering.entrySize member).1
      have := (Lowering.entrySize member).2
      (key.compile stages, value.compile stages))
  | .index receiver subscript =>
    compileIndex target (receiver.compile stages) (subscript.compile stages)
  | .callPos callee arguments =>
    let operands := arguments.attach.map fun arg =>
      have := List.sizeOf_lt_of_mem arg.property
      arg.val.compile stages
    compileCall target (stages.plain (argumentSlot 0) callee) ⟨arguments.length, [], false, false⟩ operands
  | .call callee positional keywords star starStar =>
    let operands := (Lowering.argumentExprs positional keywords star starStar).attach.map fun arg =>
      have := callOperandSize callee positional keywords star starStar arg.property
      arg.val.compile stages
    compileCall target (callee.compile stages (argumentSlot 0))
      (Lowering.argumentShape positional keywords star starStar) operands
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

module

public import Silmaril.Languages.Starlark.Functions.Lowering.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Comprehensions

open Lists.Iteration (LoopTarget)

/-- The required first generator is stored separately from the remaining clauses. -/
inductive Tail where
  | yield (value : Lowering.Expr)
  | filter (test : Lowering.Expr) (rest : Tail)
  | forIn (target : LoopTarget) (iterable : Lowering.Expr) (rest : Tail)

def Tail.operands : Tail → List Lowering.Expr
  | .yield value => [value]
  | .filter test rest => test :: rest.operands
  | .forIn _ iterable rest => iterable :: rest.operands

structure ListComp where
  locals : List Binding
  target : LoopTarget
  iterable : Lowering.Expr
  rest : Tail

/-- Private names cannot occur in normalized source identifiers. -/
def resultSlot : Binding := ⟨.global, "$comp-result"⟩
def operandSlot : Binding := ⟨.global, "$comp-operand"⟩

def appendResult : Body :=
  .evalExpr (.atom (.append (.read (.bound resultSlot)) (.read (.bound operandSlot))))

def returnResult : Body := .returnExpr (.atom (.read (.bound resultSlot)))

abbrev Stage := Binding → Lowering.Expr → Body

def stageLowered (start : Nat) : Stage := fun target expr =>
  let scratch := Lowering.temporary start
  let lowered := Lowering.lower expr scratch (start + 1)
  .assignScoped target [] (.seq lowered.code (.returnExpr (.atom (.read (.bound scratch)))))

def Tail.compile (stage : Stage) : Tail → Body
  | .yield value => .seq (stage operandSlot value) appendResult
  | .filter test rest =>
    .seq (stage operandSlot test)
      (.branch (.read (.bound operandSlot)) (rest.compile stage) (.total (.atomic .pass)))
  | .forIn target iterable rest =>
    .seq (stage operandSlot iterable) (.forIn target (.read (.bound operandSlot)) (rest.compile stage))

/-- The accumulator exists while the first iterable evaluates in the enclosing
scope. Install the comprehension's lexical slots only after that evaluation. -/
def ListComp.compile (comp : ListComp) (target : Binding) (stage : Stage) : Body :=
  .assignScoped target [resultSlot, operandSlot]
    (.seq (stage resultSlot (.atom (.list .empty)))
      (.seq (stage operandSlot comp.iterable)
        (.seq (.assignScoped resultSlot comp.locals
          (.seq (.forIn comp.target (.read (.bound operandSlot)) (comp.rest.compile stage)) returnResult))
          returnResult)))

def ListComp.body (comp : ListComp) (target : Binding) : Body :=
  comp.compile target Body.assignExpr

/-- Lower each operand within a scratch scope. On either exit that scope
restores the component's lexical frame before control reaches the next clause. -/
def ListComp.lower (comp : ListComp) (target : Binding) (start : Nat := 0) : Body :=
  comp.compile target (stageLowered start)

end Silmaril.Languages.Starlark.Functions.Comprehensions

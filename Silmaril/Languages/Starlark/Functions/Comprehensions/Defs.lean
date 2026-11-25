module

public import Silmaril.Languages.Starlark.Functions.Lowering.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Comprehensions

open Lists.Iteration (LoopTarget)

/-- The required first generator is stored separately from the remaining clauses. -/
inductive Tail (Yield : Type := Lowering.Expr) where
  | yield (value : Yield)
  | filter (test : Lowering.Expr) (rest : Tail Yield)
  | forIn (target : LoopTarget) (iterable : Lowering.Expr) (rest : Tail Yield)

def Tail.operandsWith {Yield : Type} (operands : Yield → List Lowering.Expr) :
    Tail Yield → List Lowering.Expr
  | .yield value => operands value
  | .filter test rest => test :: rest.operandsWith operands
  | .forIn _ iterable rest => iterable :: rest.operandsWith operands

def Tail.operands (tail : Tail) : List Lowering.Expr :=
  tail.operandsWith fun value => [value]

structure ListComp where
  locals : List Binding
  target : LoopTarget
  iterable : Lowering.Expr
  rest : Tail

structure DictComp where
  locals : List Binding
  target : LoopTarget
  iterable : Lowering.Expr
  rest : Tail (Lowering.Expr × Lowering.Expr)

def DictComp.operands (comp : DictComp) : List Lowering.Expr :=
  comp.rest.operandsWith fun (key, value) => [key, value]

/-- Private names cannot occur in normalized source identifiers. -/
def resultSlot : Binding := ⟨.global, "$comp-result"⟩
def operandSlot : Binding := ⟨.global, "$comp-operand"⟩
def keySlot : Binding := ⟨.global, "$comp-key"⟩

def appendResult : Body :=
  .evalExpr (.atom (.append (.read (.bound resultSlot)) (.read (.bound operandSlot))))

/-- Operands have already run in key-then-value order. Shared indexed
assignment overwrites an existing key in place and checks hashability here. -/
def putResult : Body :=
  .total (.atomic (.setIndex (.read (.bound resultSlot)) (.read (.bound keySlot))
    (.read (.bound operandSlot))))

def returnResult : Body := .returnExpr (.atom (.read (.bound resultSlot)))

abbrev Stage := Binding → Lowering.Expr → Body

def stageLowered (start : Nat) : Stage := fun target expr =>
  let scratch := Lowering.temporary start
  let lowered := Lowering.lower expr scratch (start + 1)
  .assignScoped target [] (.seq lowered.code (.returnExpr (.atom (.read (.bound scratch)))))

def Tail.compileWith {Yield : Type} (stage : Stage) (emit : Yield → Body) : Tail Yield → Body
  | .yield value => emit value
  | .filter test rest =>
    .seq (stage operandSlot test)
      (.branch (.read (.bound operandSlot)) (rest.compileWith stage emit) (.total (.atomic .pass)))
  | .forIn target iterable rest =>
    .seq (stage operandSlot iterable)
      (.forIn target (.read (.bound operandSlot)) (rest.compileWith stage emit))

def Tail.compile (stage : Stage) (tail : Tail) : Body :=
  tail.compileWith stage fun value => .seq (stage operandSlot value) appendResult

/-- The accumulator exists while the first iterable evaluates in the enclosing
scope. Install the comprehension's lexical slots only after that evaluation. -/
def compileScoped (target : Binding) (privateSlots locals : List Binding) (first : LoopTarget)
    (initial iterable : Lowering.Expr) (stage : Stage) (rest : Body) : Body :=
  .assignScoped target (resultSlot :: operandSlot :: privateSlots)
    (.seq (stage resultSlot initial)
      (.seq (stage operandSlot iterable)
        (.seq (.assignScoped resultSlot locals
          (.seq (.forIn first (.read (.bound operandSlot)) rest) returnResult))
          returnResult)))

def ListComp.compile (comp : ListComp) (target : Binding) (stage : Stage) : Body :=
  compileScoped target [] comp.locals comp.target (.atom (.list .empty)) comp.iterable stage
    (comp.rest.compile stage)

def DictComp.compile (comp : DictComp) (target : Binding) (stage : Stage) : Body :=
  compileScoped target [keySlot] comp.locals comp.target (.atom (.dict .noEntries)) comp.iterable stage
    (comp.rest.compileWith stage fun (key, value) =>
      .seq (stage keySlot key) (.seq (stage operandSlot value) putResult))

def ListComp.body (comp : ListComp) (target : Binding) : Body :=
  comp.compile target Body.assignExpr

/-- Lower each operand within a scratch scope. On either exit that scope
restores the component's lexical frame before control reaches the next clause. -/
def ListComp.lower (comp : ListComp) (target : Binding) (start : Nat := 0) : Body :=
  comp.compile target (stageLowered start)

def DictComp.body (comp : DictComp) (target : Binding) : Body :=
  comp.compile target Body.assignExpr

def DictComp.lower (comp : DictComp) (target : Binding) (start : Nat := 0) : Body :=
  comp.compile target (stageLowered start)

end Silmaril.Languages.Starlark.Functions.Comprehensions

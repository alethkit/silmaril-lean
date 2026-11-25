module

public import Silmaril.Languages.Starlark.Functions.Lowering.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Comprehensions

open Lists.Iteration (LoopTarget)

/-- The required first generator is stored separately from the remaining clauses. -/
inductive Tail (Yield : Type := Lowering.Expr) (Operand : Type := Lowering.Expr) where
  | yield (value : Yield)
  | filter (test : Operand) (rest : Tail Yield Operand)
  | forIn (target : LoopTarget) (iterable : Operand) (rest : Tail Yield Operand)

def Tail.clauseOperands {Yield Operand : Type} : Tail Yield Operand → List Operand
  | .yield _ => []
  | .filter test rest => test :: rest.clauseOperands
  | .forIn _ iterable rest => iterable :: rest.clauseOperands

def Tail.headValue {Yield Operand : Type} : Tail Yield Operand → Yield
  | .yield value => value
  | .filter _ rest | .forIn _ _ rest => rest.headValue

theorem Tail.headValueSize {Yield Operand : Type} [SizeOf Yield] [SizeOf Operand]
    (tail : Tail Yield Operand) : sizeOf tail.headValue < sizeOf tail := by
  induction tail <;> simp_all only [headValue, Tail.yield.sizeOf_spec, Tail.filter.sizeOf_spec, Tail.forIn.sizeOf_spec] <;> omega

theorem Tail.clauseOperandSize {Yield Operand : Type} [SizeOf Yield] [SizeOf Operand]
    (tail : Tail Yield Operand) {operand : Operand} (member : operand ∈ tail.clauseOperands) :
    sizeOf operand < sizeOf tail := by
  induction tail with
  | yield => simp [clauseOperands] at member
  | filter test rest ih | forIn _ test rest ih =>
    simp only [clauseOperands, List.mem_cons] at member
    rcases member with rfl | member
    · simp <;> omega
    · have := ih member
      simp
      omega

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

/-- The head code sits at the end of the reached clause path. -/
def Tail.compileClauses {Yield Operand : Type} (head : Body) (tail : Tail Yield Operand)
    (stage : (operand : Operand) → operand ∈ tail.clauseOperands → Body) : Body :=
  match tail with
  | .yield _ => head
  | .filter test rest =>
    .seq (stage test (by simp [clauseOperands]))
      (.branch (.read (.bound operandSlot))
        (rest.compileClauses head fun operand member => stage operand (List.mem_cons_of_mem _ member))
        (.total (.atomic .pass)))
  | .forIn target iterable rest =>
    .seq (stage iterable (by simp [clauseOperands]))
      (.forIn target (.read (.bound operandSlot))
        (rest.compileClauses head fun operand member => stage operand (List.mem_cons_of_mem _ member)))

def Tail.compileWith {Yield : Type} (stage : Stage) (emit : Yield → Body) (tail : Tail Yield) : Body :=
  tail.compileClauses (emit tail.headValue) fun operand _ => stage operandSlot operand

def appendYield (element : Body) : Body :=
  .seq element appendResult

def putYield (key value : Body) : Body :=
  .seq key (.seq value putResult)

def listYield (stage : Stage) (value : Lowering.Expr) : Body :=
  appendYield (stage operandSlot value)

def dictYield (stage : Stage) (entry : Lowering.Expr × Lowering.Expr) : Body :=
  putYield (stage keySlot entry.1) (stage operandSlot entry.2)

def Tail.compile (stage : Stage) (tail : Tail) : Body :=
  tail.compileWith stage (listYield stage)

/-- Allocate the accumulator, run the first iterable in the enclosing scope,
then install the comprehension's lexical slots and enter the first cursor. -/
def compileScopedWith (target : Binding) (privateSlots locals : List Binding) (first : LoopTarget)
    (initial iterable rest : Body) : Body :=
  .assignScoped target (resultSlot :: operandSlot :: privateSlots)
    (.seq initial (.seq iterable
      (.seq (.assignScoped resultSlot locals
        (.seq (.forIn first (.read (.bound operandSlot)) rest) returnResult))
        returnResult)))

def compileScoped (target : Binding) (privateSlots locals : List Binding) (first : LoopTarget)
    (initial iterable : Lowering.Expr) (stage : Stage) (rest : Body) : Body :=
  compileScopedWith target privateSlots locals first (stage resultSlot initial) (stage operandSlot iterable) rest

def ListComp.compile (comp : ListComp) (target : Binding) (stage : Stage) : Body :=
  compileScoped target [] comp.locals comp.target (.atom (.list .empty)) comp.iterable stage
    (comp.rest.compile stage)

def DictComp.compile (comp : DictComp) (target : Binding) (stage : Stage) : Body :=
  compileScoped target [keySlot] comp.locals comp.target (.atom (.dict .noEntries)) comp.iterable stage
    (comp.rest.compileWith stage (dictYield stage))

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

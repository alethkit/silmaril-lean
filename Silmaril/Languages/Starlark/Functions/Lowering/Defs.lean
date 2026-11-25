module

public import Silmaril.Languages.Starlark.Functions.Defs

public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

/-- The prefix is outside the Starlark identifier grammar. A client composing
separately lowered expressions threads `next` through the fresh ranges. -/
@[expose] def temporary (index : Nat) : Binding := ⟨.local, "$expr" ++ toString index⟩

structure Lowered where
  code : Body
  temporaries : List Binding
  next : Nat

@[expose] def assign (target : Binding) (value : Lists.Expr) : Body :=
  .total (.atomic (.assign target value))

@[expose] def freshTemporary : StateM Nat Binding := do
  let slot := temporary (← get)
  modify (· + 1)
  return slot

@[expose] def stage (code : Binding → StateM Nat Body) : StateM Nat (Body × Lists.Expr) := do
  let slot ← freshTemporary
  return (← code slot, .read (.bound slot))

/-- Stage a key and value, then check and insert their pair. -/
@[expose] def stageEntry (dictionary : Binding) (key value : Binding → StateM Nat Body) :
    StateM Nat (List Body) := do
  let keySlot ← freshTemporary
  let first ← key keySlot
  let valueSlot ← freshTemporary
  let second ← value valueSlot
  return [first, second, .insertDictEntry dictionary keySlot valueSlot]

/-- Reassociate staged reads with their original argument positions and names. -/
@[expose] def fillArguments (shape : ArgumentShape) (reads : List Lists.Expr) : Arguments :=
  let remaining := reads.drop shape.positional
  let expansions := remaining.drop shape.keywords.length
  { positional := reads.take shape.positional
    keywords := shape.keywords.zip (remaining.take shape.keywords.length)
    star := if shape.star then expansions[0]? else none
    starStar := if shape.starStar then expansions[shape.star.toNat]? else none }

@[expose] def emit (expression : Expr) (target : Binding) : StateM Nat Body :=
  match expression with
  | .atom value => pure (assign target value)
  | .list elements => do
    let parts ← elements.attach.mapM fun element => do
      have := List.sizeOf_lt_of_mem element.property
      stage (emit element.val)
    return (parts.map Prod.fst).foldr Body.seq (assign target (.list (operandList (parts.map Prod.snd))))
  | .tuple elements => do
    let parts ← elements.attach.mapM fun element => do
      have := List.sizeOf_lt_of_mem element.property
      stage (emit element.val)
    return (parts.map Prod.fst).foldr Body.seq (assign target (.tuple (operandList (parts.map Prod.snd))))
  | .dict entries => do
    let dictionary ← freshTemporary
    let steps ← entries.attach.mapM fun ⟨(key, value), member⟩ => do
      have := (entrySize member).1
      have := (entrySize member).2
      stageEntry dictionary (emit key) (emit value)
    return .seq (assign dictionary (.dict .noEntries))
      (steps.flatten.foldr Body.seq (assign target (.read (.bound dictionary))))
  | .index receiver subscript => do
    let (first, value) ← stage (emit receiver)
    let (second, index) ← stage (emit subscript)
    return .seq first (.seq second (assign target (.index value index)))
  | .slice receiver start stop stride => do
    let parts ← [receiver, start, stop, stride].attach.mapM fun operand => do
      have := sliceOperandSize operand.property
      stage (emit operand.val)
    return (parts.map Prod.fst).foldr Body.seq (assign target (.slice (operandList (parts.map Prod.snd))))
  | .call callee positional keywords star starStar => do
    let (before, callable) ← stage (emit callee)
    let parts ← (argumentExprs positional keywords star starStar).attach.mapM fun part => do
      have := argumentSize callee positional keywords star starStar part.property
      stage (emit part.val)
    let args := fillArguments (argumentShape positional keywords star starStar) (parts.map Prod.snd)
    return .seq before ((parts.map Prod.fst).foldr Body.seq (.call (some target) callable args))
  | .branch test yes no => do
    let (before, condition) ← stage (emit test)
    return .seq before (.branch condition (← emit yes target) (← emit no target))
  | .logical op left right => do
    let (first, saved) ← stage (emit left)
    let second ← emit right target
    let keep := assign target saved
    let branch := match op with
      | .and => Body.branch saved second keep
      | .or => Body.branch saved keep second
    return .seq first branch
termination_by sizeOf expression
decreasing_by all_goals first | assumption | (simp_wf; omega)

/-- Lower into a caller-chosen destination that is distinct from scratch names.
The returned names can use the frame's direct bindings for exact heap
comparison. Only a successful expression writes the destination. -/
@[expose] def lower (expression : Expr) (target : Binding) (start : Nat := 0) : Lowered :=
  let (code, stop) := (emit expression target).run start
  ⟨code, (List.range' start (stop - start)).map temporary, stop⟩

/-- Stage a loop operand once before entering the existing checked body. -/
@[expose] def lowerForIn (target : Binding) (iterable : Expr) (body : Body) (start : Nat := 0) : Lowered :=
  let operand := temporary start
  let staged := lower iterable operand (start + 1)
  ⟨.seq staged.code (.forIn target (.read (.bound operand)) body),
    operand :: staged.temporaries, staged.next⟩

end Silmaril.Languages.Starlark.Functions.Lowering

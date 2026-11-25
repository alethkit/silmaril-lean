module

public import Silmaril.Languages.Starlark.Functions.Lowering.Syntax.Defs

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

@[expose] def stage (code : Binding → StateM Nat Body) : StateM Nat (Body × Lists.Expr) := do
  let slot := temporary (← get)
  modify (· + 1)
  return (← code slot, .read (.bound slot))

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

end Silmaril.Languages.Starlark.Functions.Lowering

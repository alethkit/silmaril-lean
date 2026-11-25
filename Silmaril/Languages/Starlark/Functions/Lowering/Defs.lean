module

public import Silmaril.Languages.Starlark.Functions.Defs

public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

/-- Resolved expressions that can nest calls, branch, or short-circuit.
An atom uses the existing call-free collection expression language. -/
inductive Expr where
  | atom (expression : Lists.Expr)
  | call (callee : Expr) (positional : List Expr) (keywords : List (String × Expr))
      (star starStar : Option Expr)
  | branch (test yes no : Expr)
  | logical (op : LogicalOp) (left right : Expr)

def Expr.callPos (callee : Expr) (positional : List Expr) : Expr :=
  .call callee positional [] none none

/-- The prefix is outside the Starlark identifier grammar. A client composing
separately lowered expressions threads `next` through the fresh ranges. -/
def temporary (index : Nat) : Binding := ⟨.local, "$expr" ++ toString index⟩

structure Lowered where
  code : Body
  temporaries : List Binding
  next : Nat

private def assign (target : Binding) (value : Lists.Expr) : Body :=
  .total (.atomic (.assign target value))

private def stage (code : Binding → StateM Nat Body) : StateM Nat (Body × Lists.Expr) := do
  let slot := temporary (← get)
  modify (· + 1)
  return (← code slot, .read (.bound slot))

private theorem keywordSize (keyword : String × Expr) : sizeOf keyword.2 ≤ sizeOf keyword := by
  cases keyword
  simp

private def emit (expression : Expr) (target : Binding) : StateM Nat Body :=
  match expression with
  | .atom value => pure (assign target value)
  | .call callee positional keywords star starStar => do
    let (before, callable) ← stage (emit callee)
    let positions ← positional.attach.mapM fun part => do
      have := List.sizeOf_lt_of_mem part.property
      stage (emit part.val)
    let named ← keywords.attach.mapM fun part => do
      have := List.sizeOf_lt_of_mem part.property
      have := keywordSize part.val
      return (part.val.1, ← stage (emit part.val.2))
    let spread ← match star with
      | none => pure none
      | some value => some <$> stage (emit value)
    let mapping ← match starStar with
      | none => pure none
      | some value => some <$> stage (emit value)
    let args : Arguments :=
      { positional := positions.map Prod.snd
        keywords := named.map (fun (name, (_, value)) => (name, value))
        star := spread.map Prod.snd
        starStar := mapping.map Prod.snd }
    let prefixes := positions.map Prod.fst ++ named.map (fun (_, (code, _)) => code) ++
      spread.toList.map Prod.fst ++ mapping.toList.map Prod.fst
    return .seq before (prefixes.foldr Body.seq (.call (some target) callable args))
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
decreasing_by all_goals (simp_wf; omega)

/-- Lower into a caller-chosen destination. Install the returned temporary
slots in the enclosing function or root frame before execution. Only the final
value writes the destination, even when an intermediate call fails. -/
def lower (expression : Expr) (target : Binding) (start : Nat := 0) : Lowered :=
  let (code, stop) := (emit expression target).run start
  ⟨code, (List.range' start (stop - start)).map temporary, stop⟩

end Silmaril.Languages.Starlark.Functions.Lowering

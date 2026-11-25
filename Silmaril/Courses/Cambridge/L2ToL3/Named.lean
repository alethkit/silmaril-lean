module

public import Silmaril.Courses.Cambridge.L2ToL3.Defs
public import Silmaril.Courses.Cambridge.L3.Concrete

/-! Named L2 syntax embeds before scope resolution, with the same layout as the
resolved CBV translation. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2ToL3

/-- Preserve variable and binder spellings. A named L2 cell becomes an
explicit L3 address expression, even when a variable has the same spelling. -/
def named (address : Layout) : L2.RawExpr → L3.RawExpr
  | .int n => .int n
  | .bool b => .bool b
  | .binary left op right => .binary (named address left) op (named address right)
  | .cond test yes no => .cond (named address test) (named address yes) (named address no)
  | .assign loc value => .assign (.loc (address loc)) (named address value)
  | .deref loc => .deref (.loc (address loc))
  | .skip => .skip
  | .seq left right => .seq (named address left) (named address right)
  | .loop test body => .loop (named address test) (named address body)
  | .var name => .var name
  | .lam name domain body => .lam name (ty domain) (named address body)
  | .app fn arg => .app (named address fn) (named address arg)
  | .letE name type value body => .letE name (ty type) (named address value) (named address body)
  | .letRecFun fn param domain codomain fnBody body =>
      .letRecFun fn param (ty domain) (ty codomain) (named address fnBody) (named address body)

/-- Both resolvers use the same ambient binder list, including its shadowing
order. Names outside it and the enclosing binders stay free. -/
theorem resolve_named (address : Layout) (term : L2.RawExpr) (bound : List L2.Var) :
    (named address term).resolve bound = expr address (term.resolve bound) := by
  induction term generalizing bound with
  | var name =>
    simp only [named, L2.RawExpr.resolve, L3.RawExpr.resolve]
    cases bound.idxOf? name <;> rfl
  | _ => simp [named, L2.RawExpr.resolve, L3.RawExpr.resolve, expr, *]

/-- A named image with valid L3 spellings can use the existing canonical
printer. The public closed-scope parser then returns the resolved embedding. -/
theorem parseResolved_print_named (address : Layout) (term : L2.RawExpr)
    (spellable : L3.Concrete.NamesOk (named address term)) :
    L3.Concrete.parseResolved (L3.Concrete.print ⟨named address term, spellable⟩) =
      some (expr address (term.resolve [])) := by
  rw [L3.Concrete.parseResolved_print]
  exact congrArg some (resolve_named address term [])

end Silmaril.Courses.Cambridge.L2ToL3

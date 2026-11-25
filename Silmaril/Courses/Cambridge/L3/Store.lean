module

public import Silmaril.Courses.Cambridge.L3.Syntax
public import Mathlib.Data.Finmap

/-! # Cambridge L3 values and finite stores (§5.5, p. 78) -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

inductive IsValue : Expr → Prop where
  | int (n : Int) : IsValue (.int n)
  | bool (b : Bool) : IsValue (.bool b)
  | skip : IsValue .skip
  | loc (loc : Loc) : IsValue (.loc loc)
  | lam (domain : Ty) (body : Expr) : IsValue (.lam domain body)
  | pair {left right : Expr} : IsValue left → IsValue right → IsValue (.pair left right)
  | inl {e : Expr} {T : Ty} : IsValue e → IsValue (.inl e T)
  | inr {e : Expr} {T : Ty} : IsValue e → IsValue (.inr e T)
  | record {labels : RecordLabels} {fields : labels.Index → Expr} :
      (∀ i, IsValue (fields i)) → IsValue (.record labels fields)

abbrev Value := { e : Expr // IsValue e }
abbrev Store := Finmap (fun _ : Loc => Value)

structure Config where
  expr : Expr
  store : Store

end Silmaril.Courses.Cambridge.L3

module

public import Silmaril.Cerberus.Ctype.Defs

/-!
# A restricted C typing judgment: the operands of `+` (C11 §6.5.6¶2)

`AdditiveOperands t₁ t₂`: the constraint of C11 §6.5.6¶2 on the operand types of binary `+`,
"either both operands shall have arithmetic type, or one operand shall be a pointer to a complete
object type and the other shall have integer type", over Cerberus's `Ctype` (after lvalue
conversion; qualifiers and annotations ignored).

This is the **only** typing judgment the explorer states: it is not a typing judgment for C
programs. Completeness of object types is approximated by excluding `void`, function types and
incomplete arrays (struct and union completeness, which needs the tag environment, is not
modelled: a pointer to a struct counts as a pointer to a complete object). A type-error
certificate for a program is a proof of `¬ AdditiveOperands t₁ t₂` for the operand types of one
`+` in it; that those *are* its operand types is a separate link (the Lean frontend does not yet
type binary operands, so today it is read from the declarations, not checked).
-/

@[expose] public section

namespace Silmaril.Project.Shapes.C

open Silmaril.Cerberus

/-- An integer type (`_Bool`, `char`, signed and unsigned integers, enumerations). -/
def IsIntegerType : Ctype → Prop
  | .mk _ (.basic (.integer _)) => True
  | _ => False

/-- An arithmetic type: integer or real floating. -/
def IsArithmeticType : Ctype → Prop
  | .mk _ (.basic _) => True
  | _ => False

/-- A pointer to a complete object type (approximated: not `void`, not a function, not an
array of unknown size). -/
def IsObjectPointerType : Ctype → Prop
  | .mk _ (.pointer _ (.mk _ .void)) => False
  | .mk _ (.pointer _ (.mk _ (.function ..))) => False
  | .mk _ (.pointer _ (.mk _ (.functionNoParams _))) => False
  | .mk _ (.pointer _ (.mk _ (.array _ none))) => False
  | .mk _ (.pointer _ _) => True
  | _ => False

/-- **C11 §6.5.6¶2, for `+`.** -/
inductive AdditiveOperands : Ctype → Ctype → Prop where
  | arith {t₁ t₂ : Ctype} : IsArithmeticType t₁ → IsArithmeticType t₂ → AdditiveOperands t₁ t₂
  | ptrInt {t₁ t₂ : Ctype} : IsObjectPointerType t₁ → IsIntegerType t₂ → AdditiveOperands t₁ t₂
  | intPtr {t₁ t₂ : Ctype} : IsIntegerType t₁ → IsObjectPointerType t₂ → AdditiveOperands t₁ t₂

/-- `int`. -/
def intCtype : Ctype := .mk [] (.basic (.integer (.signed .int)))

/-- `int *`. -/
def intPtrCtype : Ctype := .mk [] (.pointer ⟨false, false, false⟩ intCtype)

end Silmaril.Project.Shapes.C

end

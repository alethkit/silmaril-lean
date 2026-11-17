module

public import Silmaril.Project.Shapes.C.Additive.Thms
public import Silmaril.Project.Shapes.C.Defs
public meta import Silmaril.Project.Shapes.C.Defs

/-!
# A type-error certificate under a restricted judgment

`examples/compiler-explorer/typeerror/addp.c` adds two `int *` parameters. The certificate is a
kernel-checked proof that this pair of operand types violates C11 §6.5.6¶2
(`Silmaril.Project.Shapes.C.AdditiveOperands`), the only typing judgment stated here.

The link from the C text to the operand types is **not** checked: the Lean frontend does not yet
type binary operands. Run on the text (compiled evaluation, `#guard` below) it stops with
"typing not yet ported: binary operands (§6.5.5-6.5.12)", neither accepting nor rejecting the
program. The types are the declared types of `p` and `q`.
-/

@[expose] public section

namespace CompilesToExamples.Explorer.TypeError

open Silmaril.Project.Shapes.C

/-- The C text, verbatim. -/
def cText : String :=
  "/* Two pointers added: C11 6.5.6p2 allows pointer + integer, never pointer + pointer. */\nint *addp(int *p, int *q)\n{\n  return p + q;\n}\n"

-- The frontend does not decide this program (compiled evaluation, not a proof).
#guard match FrontendAil cText with
  | .error e => e == "typing: Silmaril: typing not yet ported: binary operands (§6.5.5-6.5.12)"
  | .ok _ => false

/-- **The operands of `p + q` (`int *`, `int *`) violate C11 §6.5.6¶2.** -/
theorem addp_operands : ¬ AdditiveOperands intPtrCtype intPtrCtype := AdditiveOperands.not_ptr_ptr

end CompilesToExamples.Explorer.TypeError

end

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Defs

/-! # Native emit prefixes for the selected reply tables -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

/-- Emit in order, then enter the original region with its input retained. -/
def prependEmits : List Bool → Region signature.Instr → Region signature.Instr
  | [], r => r
  | b :: bs, r => .let₁ (.op (show signature.Instr from Op.emit b) .unit)
      ((prependEmits bs r).renameVars Nat.succ)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

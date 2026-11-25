module

public import Silmaril.Languages.Python.Core.Rules.Defs
public import Silmaril.Languages.Python.Core.Thms
import Silmaril.Proofs.Languages.Python.Core.Rules.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Rules

theorem primitive_iff {op : BinOp} {left right : Int} {result : Completion} :
    Derives (.primitive op left right result) ↔ op.Eval left right result :=
  Proofs.Languages.Python.Core.Rules.primitive_iff

theorem expression_iff {source : Expr} {next : Except Exception Expr} :
    Derives (.expression source next) ↔ source.Step next :=
  Proofs.Languages.Python.Core.Rules.expression_iff

/-- The least rule model and the typed machine have the same labelled edges. -/
theorem step_iff {source target : State} {label : Option Completion} :
    Derives (.edge source label target) ↔ Step source label target :=
  Proofs.Languages.Python.Core.Rules.step_iff

theorem deterministic {source first second : State} {label other : Option Completion}
    (firstEdge : Derives (.edge source label first)) (secondEdge : Derives (.edge source other second)) :
    label = other ∧ first = second :=
  Step.deterministic (step_iff.mp firstEdge) (step_iff.mp secondEdge)

end Silmaril.Languages.Python.Core.Rules

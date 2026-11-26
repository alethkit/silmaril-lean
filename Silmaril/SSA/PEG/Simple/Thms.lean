module

public import Silmaril.SSA.PEG.Simple.Translate
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Graph
import Silmaril.Proofs.SSA.PEG.Simple.Source
import Silmaril.Proofs.SSA.PEG.Simple.Translation

public section

namespace Silmaril.SSA.PEG.Simple

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params nodes vars outs : List (Ty Data)} {result : Ty Data}

/-- Finite source execution has a unique outcome, including finite failure. -/
theorem Exec.deterministic {model : Interpretation.{u,v,w} P} {loops : Bool}
    {s : Stmt P loops vars outs} {store : Tuple model.Value vars}
    {a b : Option (Tuple model.Value outs)}
    (first : Exec model s store a) (second : Exec model s store b) : a = b :=
  Proofs.deterministic first second

/-- A closed builder gives a PEG whose edges lead strictly to earlier emissions. -/
theorem Code.toGraph_wellFormed (code : Code P params [] nodes) (outputs : Tuple (Port nodes) outs) :
    (code.toGraph outputs).WellFormed :=
  Proofs.toGraph_wellFormed code outputs

/-- The emission-order account solves the actual Figure 11 equations of the numbered graph. -/
theorem Code.observe_toGraph (code : Code P params [] nodes) (outputs : Tuple (Port nodes) outs)
    (model : Interpretation.{u,v,w} P) (input : Tuple model.Value params)
    (wf : WellFounded (code.toGraph outputs).Demand) (i : Index 0) :
    (code.toGraph outputs).observe model ((code.toGraph outputs).denote model input wf) i =
      select (code.eval model input .nil) outputs :=
  Proofs.observe_toGraph model input code outputs wf i

/-- A successful execution preserves every live output slot. The initial
node context must realize the initial source store. -/
theorem Stmt.lower_correct (s : Stmt P false vars outs) (ctx : Tuple (Port nodes) vars)
    (model : Interpretation.{u,v,w} P) (input : Tuple model.Value params)
    (values : Tuple (fun t => Option (model.Value t)) nodes)
    {store : Tuple model.Value vars} {final : Tuple model.Value outs}
    (entry : Realizes model values ctx store) (run : Exec model s store (some final)) :
    let b := s.lower (params := params) ctx
    Realizes model (b.code.eval model input values) b.refs final :=
  Proofs.stmt_correct model input s ctx values entry run

theorem Program.translate_wellFormed (p : Program P false params result) : p.translate.WellFormed :=
  p.lower.code.toGraph_wellFormed p.lower.refs

/-- The loop-free direction of the paper's Theorem 2. A successful source
return gives a defined root of the graph computed by `Program.translate`. -/
theorem Program.translate_returns (p : Program P false params result) (model : Interpretation.{u,v,w} P)
    (input : Tuple model.Value params) {value : model.Value result} (run : p.Returns model input value)
    (i : Index 0) :
    p.translate.observe model
      (p.translate.denote model input (p.translate.demandWellFounded p.translate_wellFormed)) i =
      .cons (some value) .nil :=
  Proofs.program_correct model input p run _ i

end Silmaril.SSA.PEG.Simple

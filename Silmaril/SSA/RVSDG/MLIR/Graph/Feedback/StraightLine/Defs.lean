module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Defs

/-! Interpret an ordered MLIR block with an effectful primitive model. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Feedback

open OrderedRuntime.Structured (Values)

universe u v w z
variable {V : Type u} {Op : Dialect.{u,v} V PUnit.{u+1}}

/-- The admitted fragment consists of primitive bindings and a final yield. -/
def Code.StraightLine : {scope : List (Ports (PortSort V))} → {outs : Ports (PortSort V)} →
    Code Op scope outs → Prop
  | _, _, .yield _ => True
  | _, _, .prim _ _ rest => rest.StraightLine
  | _, _, .choose .. | _, _, .feedback .. => False

/-- Execute every binding in order, including operations with empty result
tuples. The primitive interpretation supplies the effects. -/
def Code.runStraightLine {M : Type (max u w) → Type z} [Monad M] {value : V → Type w}
    (step : ∀ {ins results}, Op ins results → Tuple (Values value) ins → M (Tuple (Values value) results)) :
    {scope : List (Ports (PortSort V))} → {outs : Ports (PortSort V)} →
    (code : Code Op scope outs) → code.StraightLine → Locals (Values value) scope → M (Tuple (Values value) outs)
  | _, _, .yield values, _, env => pure (values.read .nil env)
  | _, _, .prim op args rest, admitted, env => do
    let result ← step op (args.read .nil env)
    runStraightLine step rest admitted (env.snoc result)
  | _, _, .choose .., admitted, _ => False.elim admitted
  | _, _, .feedback .., admitted, _ => False.elim admitted

end Silmaril.SSA.RVSDG.MLIR.Graph.Feedback

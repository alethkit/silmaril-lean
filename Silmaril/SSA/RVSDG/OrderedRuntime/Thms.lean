module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Defs
public import Silmaril.SSA.RVSDG.Thms
import Silmaril.Proofs.SSA.RVSDG.OrderedRuntime.Agreement

/-! # Observation of a linear runtime chain -/

public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime

open CategoryTheory Silmaril.RuntimeWires
open Silmaril.RuntimeWires.Presentation (Computations)

universe u v w
variable {G : EffectfulPolygraph.{u, v}}
variable {A B : List G.Obj} {sigs : List (Ports (Ty G))}

/-- The ordered composition in types reproduces the entire operational tuple. -/
theorem denoteFunctions_run (m : Model.{u, v, w} G)
    (g : Graph (Opcode G) (ports G A) [] sigs (ports G B))
    (h : Chain G A B .entry g.toTerm) (input : Tuple m.Val (ports G A)) :
    denoteFunctions m g h input = g.run m.toRVSDG input :=
  Proofs.denoteFunctions_run m g h input

/-- Any realization of the runtime presentation with the specified generator
interpretations agrees with the runnable graph on its admitted chain. -/
theorem denote_run (m : Model.{u, v, w} G) (F : Computations G ⥤ Type (max u w))
    (e : Realization m F) (g : Graph (Opcode G) (ports G A) [] sigs (ports G B))
    (h : Chain G A B .entry g.toTerm) (input : Tuple m.Val (ports G A)) :
    F.map (denote g h) (e.encode A input) = e.encode B (g.run m.toRVSDG input) :=
  Proofs.denote_run m F e g h input

end Silmaril.SSA.RVSDG.OrderedRuntime

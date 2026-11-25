module

public import Silmaril.Semantics.RuntimeWires.Presentation.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.Presentation.Conservation

public section

namespace Silmaril.RuntimeWires.Presentation

universe u v

/-- The generators and operations preserve the number of runtime wires. -/
theorem preservesRuntime {G : EffectfulPolygraph.{u,v}} {A B : List (Wire G.Obj)}
    (f : Diagram (signature G) A B) : runtimeCount A = runtimeCount B :=
  Proofs.preservesRuntime f

/-- There are no runtime morphisms between boundaries with different runtime counts. -/
theorem homPreservesRuntime {G : EffectfulPolygraph.{u,v}} {A B : List (Wire G.Obj)}
    (f : Hom G A B) : runtimeCount A = runtimeCount B :=
  Proofs.homPreservesRuntime f

end Silmaril.RuntimeWires.Presentation

module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.RuntimeReadout.Thms

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory Presentation
open scoped MonoidalCategory

universe u v

/-- A geometric cap with a single runtime at the indicated position
among its ordered value contacts. -/
structure PositionedRuntimeCap (G : EffectfulPolygraph.{u,v}) where
  cap : FixedCap (signature G)
  word : List G.Obj
  position : Position word
  types : cap.types = (placed word position).word

namespace FixedRuntimeCap

variable {G : EffectfulPolygraph.{u,v}}

/-- Place only passive value contacts to the right of the runtime drawing. -/
def padRight (X : FixedRuntimeCap G) (P : FixedCap (signature G)) {W : List G.Obj}
    (types : P.types = values W) : FixedRuntimeCap G where
  cap := X.cap.beside P
  word := X.word ++ W
  types := (FixedCap.beside_labels X.cap P).trans (by
    change X.cap.types ++ P.types = none :: values (X.word ++ W)
    rw [X.types, types]
    simp only [values, List.map_append, List.cons_append])

end FixedRuntimeCap

namespace PositionedRuntimeCap

variable {G : EffectfulPolygraph.{u,v}}

/-- Transport the sweep's actual ordered cap to the indicated clique object. -/
def boundaryIso (X : PositionedRuntimeCap G) :
    (FixedCap.runtimeSweep G).obj X.cap ≅ placed X.word X.position :=
  eqToIso (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) X.types)

variable {X Y : PositionedRuntimeCap G}

/-- Read the actual component at the drawn runtime positions. -/
def component (f : X.cap ⟶ Y.cap) :
    (braidClique X.word).obj X.position ⟶ (braidClique Y.word).obj Y.position :=
  X.boundaryIso.inv ≫ (FixedCap.runtimeSweep G).map f ≫ Y.boundaryIso.hom

/-- Reconstruct the clique family from the component at the drawn positions. -/
def readClique (f : X.cap ⟶ Y.cap) : Clique.Hom (braidClique X.word) (braidClique Y.word) :=
  (Clique.componentEquiv (braidClique X.word) (braidClique Y.word) X.position Y.position).symm
    (component f)

end PositionedRuntimeCap

/-- A generator drawn as one point vertex, with no bypass at its height.
These hypotheses specify the geometry of a crossing before it is read. -/
structure IsolatedRuntimeGenerator {G : EffectfulPolygraph.{u,v}} (e : Edge G)
    (A B : FixedCap (signature G)) where
  drawing : FixedDrawing (signature G) A.profile B.profile
  vertex : Fin drawing.vertices
  only : ∀ j, j = vertex
  label : drawing.drawing.generator vertex = e
  noThrough : ∀ w, ¬ drawing.drawing.crosses w (drawing.drawing.vertexHeight vertex)

end Silmaril.RuntimeWires.ProgressiveGraph

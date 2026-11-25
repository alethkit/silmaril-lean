module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapWhiskering.Thms
public import Silmaril.Semantics.RuntimeWires.Coherence.Thms

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory Presentation

universe u v

/-- A fixed geometric cap of the runtime signature with one runtime wire
in the leftmost slot. Its morphisms already draw the runtime explicitly. -/
structure FixedRuntimeCap (G : EffectfulPolygraph.{u,v}) where
  cap : FixedCap (signature G)
  word : List G.Obj
  types : cap.types = none :: values word

namespace FixedRuntimeCap

variable {G : EffectfulPolygraph.{u,v}}

instance : Category (FixedRuntimeCap G) where
  Hom X Y := X.cap ⟶ Y.cap
  id X := 𝟙 X.cap
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

def ofDrawing {X Y : FixedRuntimeCap G}
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) : X ⟶ Y :=
  FixedCap.ofDrawing p

/-- Retain the geometric drawing and forget the leftmost-runtime witness. -/
def toFixedCap (G : EffectfulPolygraph.{u,v}) : FixedRuntimeCap G ⥤ FixedCap (signature G) where
  obj := cap
  map f := f

/-- Impose the runtime's crossing equations after reading the same typed terms. -/
def termToRuntime (G : EffectfulPolygraph.{u,v}) :
    Diagram.Presented (signature G) (Sliced.noEquations (signature G)) ⥤ Runtime G :=
  Diagram.Presented.imposeEquations (fun h => h.elim)

end FixedRuntimeCap

/-- Read a drawing over the runtime signature and impose the crossing equations. -/
def FixedCap.runtimeSweep (G : EffectfulPolygraph.{u,v}) : FixedCap (signature G) ⥤ Runtime G :=
  FixedCap.toSliced (signature G) ⋙
    Sliced.Presented.toTerms (signature G) ⋙ FixedRuntimeCap.termToRuntime G

namespace FixedRuntimeCap

variable {G : EffectfulPolygraph.{u,v}}

def toRuntime (G : EffectfulPolygraph.{u,v}) : FixedRuntimeCap G ⥤ Runtime G :=
  toFixedCap G ⋙ FixedCap.runtimeSweep G

def computation (X : FixedRuntimeCap G) : Computations G := ⟨X.word⟩

/-- Identify the read cap with the chosen component of its braid clique. -/
def boundaryIso (X : FixedRuntimeCap G) : (toRuntime G).obj X ≅ X.computation.boundary :=
  eqToIso (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) X.types)

/-- Geometric readout as a leftmost braid-clique component. -/
def toComputations (G : EffectfulPolygraph.{u,v}) : FixedRuntimeCap G ⥤ Computations G where
  obj := computation
  map {X Y} f := show X.computation.boundary ⟶ Y.computation.boundary from
    X.boundaryIso.inv ≫ (toRuntime G).map (X := X) (Y := Y) f ≫ Y.boundaryIso.hom
  map_id X := by
    change X.boundaryIso.inv ≫ (toRuntime G).map (𝟙 X) ≫ X.boundaryIso.hom =
      𝟙 X.computation.boundary
    rw [(toRuntime G).map_id]
    simp
  map_comp := by
    intro X Y Z f g
    let F := toRuntime G
    change X.boundaryIso.inv ≫ F.map (X := X) (Y := Z) (f ≫ g) ≫ Z.boundaryIso.hom =
      (X.boundaryIso.inv ≫ F.map (X := X) (Y := Y) f ≫ Y.boundaryIso.hom) ≫
        (Y.boundaryIso.inv ≫ F.map (X := Y) (Y := Z) g ≫ Z.boundaryIso.hom)
    rw [F.map_comp]
    simp [Category.assoc]

/-- Reconstruct the morphism at every allowed pair of runtime positions. -/
def readClique {X Y : FixedRuntimeCap G} (f : X ⟶ Y) :
    Clique.Hom (braidClique X.word) (braidClique Y.word) :=
  Computations.cliqueHom (A := X.computation) (B := Y.computation) ((toComputations G).map f)

end FixedRuntimeCap
end Silmaril.RuntimeWires.ProgressiveGraph

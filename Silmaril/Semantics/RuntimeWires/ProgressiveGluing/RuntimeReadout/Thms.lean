module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.RuntimeReadout.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.RuntimeReadout.Maps

public noncomputable section

/-!
# Reading an explicit runtime as a braid-clique morphism

The comparison starts with drawings over the runtime signature of
Definition 3.8 and Figure 8. The cap word has the displayed runtime at its
leftmost slot. The existing geometric readout passes through the sliced and
free term presentations and then imposes the crossing equations of Figure 9.
The boundary isomorphisms identify these runtime arrows with the leftmost
components of Definitions 3.9–3.10 and Lemma 3.11. The checked component
equivalence reconstructs the other positions.

For Figure 10, right whiskering uses the straight **value** strands beside
the active runtime diagram. The corresponding geometric-to-sliced law is
`FixedCap.toSliced_whiskerRight`. Left whiskering in
`Presentation.Computations.whiskerLeft` uses braidings on both ends of the
active diagram in addition to the padding compared by
`FixedCap.toSliced_whiskerLeft`.

This is a comparison on fixed-contact classes with explicit runtime traces,
toward Corollary 3.15 of Román and Sobociński, arXiv:2305.06075v5.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap

open CategoryTheory Presentation

universe u v
variable {G : EffectfulPolygraph.{u,v}} {X Y : FixedRuntimeCap G}

/-- The readout through sliced sheets and terms agrees with reading the
chosen component in the runtime category. -/
def comparison (G : EffectfulPolygraph.{u,v}) :
    toRuntime G ≅ toComputations G ⋙ Computations.inRuntime G :=
  NatIso.ofComponents boundaryIso (fun f => by exact Proofs.RuntimeReadout.naturality f)

theorem readClique_leftmost (f : X ⟶ Y) :
    (readClique f).app 0 0 = (toComputations G).map f :=
  Computations.cliqueHom_leftmost _

/-- The actual sweep of a single effect vertex with no bypass strands
reads as the generator with its runtime input and output already drawn. -/
theorem map_effect (e : G.effect.Edge)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) (vertex : Fin p.vertices)
    (only : ∀ j, j = vertex) (label : p.drawing.generator vertex = .effect e)
    (noThrough : ∀ w, ¬ p.drawing.crosses w (p.drawing.vertexHeight vertex))
    (input : X.word = G.effect.source e) (output : G.effect.target e = Y.word) :
    (toComputations G).map (ofDrawing p) =
      eqToHom (congrArg (Computations.mk (G := G)) input) ≫
        Computations.effect e ≫ eqToHom (congrArg (Computations.mk (G := G)) output) := by
  exact Proofs.RuntimeReadout.map_effect e p vertex only label noThrough input output

end Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

open CategoryTheory Presentation

universe u v
variable {G : EffectfulPolygraph.{u,v}} {A B : FixedCap (signature G)}

/-- Read a single isolated generator, including either runtime crossing. -/
theorem runtimeSweep_generator (e : Edge G)
    (p : FixedDrawing (signature G) A.profile B.profile) (vertex : Fin p.vertices)
    (only : ∀ j, j = vertex) (label : p.drawing.generator vertex = e)
    (noThrough : ∀ w, ¬ p.drawing.crosses w (p.drawing.vertexHeight vertex))
    (input : A.types = (signature G).source e) (output : (signature G).target e = B.types) :
    (runtimeSweep G).map (ofDrawing p) =
      eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) input) ≫
        Diagram.Presented.ofTerm (Diagram.gen (S := signature G) e) ≫
        eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) output) := by
  exact Proofs.RuntimeReadout.read_edge e p vertex only label noThrough input output

end Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

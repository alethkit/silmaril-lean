module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.BothSides.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.BothSides

public noncomputable section

/-!
# Two-sided idle placement in Figure 10

Apply the iterated left crossing construction and straight right padding in
both orders. The cuts and right idle profiles may be chosen independently.
The outer typed words agree by list associativity, and the readout square
uses mixed whiskering coherence in the runtime computations category.
This is a comparison for Lemma 3.11 and Figure 10 of Román and Sobociński,
arXiv:2305.06075v5, at the level of readout arrows.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap

open CategoryTheory Presentation

universe u v
variable {G : EffectfulPolygraph.{u,v}} {X Y : FixedRuntimeCap G} {L R : List G.Obj}

/-- The geometric right placement reads as the existing runtime whiskering. -/
theorem toComputations_padRightDrawing (P : FixedCap (signature G)) (types : P.types = values R)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    (toComputations G).map (X := X.padRight P types) (Y := Y.padRight P types)
      (ofDrawing (padRightDrawing P types p)) =
    (Computations.whiskerRight (Computations.mk R)).map
      ((toComputations G).map (X := X) (Y := Y) (ofDrawing p)) :=
  Proofs.PositionedRuntime.read_right_drawing P types p

/-- Independent valid sweeps read the right contacts as a suffix of each row. -/
theorem padRightDrawing_cellsAt (P : FixedCap (signature G)) (types : P.types = values R)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile)
    (s : p.drawing.LayerSweep) (t : (padRightDrawing P types p).drawing.LayerSweep) :
    ((padRightDrawing P types p).readSheetAt t).cells =
      (p.readSheetAt s).cells.map (· ++ (values R).map Sum.inl) :=
  Proofs.PositionedRuntime.right_cells_at P types p s t

variable {A B C D P Q : FixedCap (signature G)} {pTypes : P.types = values R} {qTypes : Q.types = values R}

/-- Both actual pairs of outer caps have the runtime, left idle word,
active word, and right idle word in the same order. -/
theorem twoSided_types (left : LeftPlacement X Y L A B)
    (right : LeftPlacement (X.padRight Q qTypes) (Y.padRight Q qTypes) L C D) :
    ((left.source.padRight P pTypes).cap.types = right.source.cap.types) ∧
      ((left.target.padRight P pTypes).cap.types = right.target.cap.types) :=
  Proofs.PositionedRuntime.mixed_types left right

/-- Read the two actual placement orders at their chosen cuts. The two
transports reparenthesize the same ordered words in `Computations`. -/
theorem toComputations_twoSided (left : LeftPlacement X Y L A B)
    (right : LeftPlacement (X.padRight Q qTypes) (Y.padRight Q qTypes) L C D)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    (toComputations G).map (X := left.source.padRight P pTypes) (Y := left.target.padRight P pTypes)
      (ofDrawing (padRightDrawing P pTypes (left.drawing p))) ≫
        eqToHom (Computations.concat_assoc (Computations.mk L) Y.computation (Computations.mk R)) =
    eqToHom (Computations.concat_assoc (Computations.mk L) X.computation (Computations.mk R)) ≫
      (toComputations G).map (X := right.source) (Y := right.target)
        (ofDrawing (right.drawing (padRightDrawing Q qTypes p))) :=
  Proofs.PositionedRuntime.read_mixed left right p

end Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedDrawing

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {A B : CapProfile O}

/-- Any valid sweep of one representative gives its typed readout sheet. -/
theorem readSheetAt_eq_readSheet (p : FixedDrawing S A B) (s : p.drawing.LayerSweep) :
    p.readSheetAt s = p.readSheet := by
  obtain ⟨same⟩ := Equivalent.refl p
  exact readSheetAt_comparison same s p.drawing.layerSweep

end Silmaril.RuntimeWires.ProgressiveGraph.FixedDrawing

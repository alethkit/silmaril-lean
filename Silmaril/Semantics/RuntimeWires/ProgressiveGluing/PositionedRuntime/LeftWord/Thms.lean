module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftWord.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftWord
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftWordCells

public noncomputable section

/-!
# Figure 10 for any finite left idle word

The representative iterates collared placements, with one incoming and
one outgoing crossing per idle value. Each step may choose its cuts
independently. The proof uses the left unit and the premonoidal associativity
of the existing runtime presentation to identify the readout with the
whole-word left whiskering of Lemma 3.11 and Figure 10 of Román and
Sobociński, arXiv:2305.06075v5.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap.LeftPlacement

open CategoryTheory Presentation

universe u v
variable {G : EffectfulPolygraph.{u,v}} {X Y : FixedRuntimeCap G}
variable {w : List G.Obj} {A B : FixedCap (signature G)}

/-- The iterated geometric representative reads as Figure 10 left
whiskering by the entire idle word in the existing runtime quotient. -/
theorem toComputations_drawing (plan : LeftPlacement X Y w A B)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    (toComputations G).map (X := plan.source) (Y := plan.target) (ofDrawing (plan.drawing p)) =
      (Computations.whiskerLeft (Computations.mk w)).map
        ((toComputations G).map (X := X) (Y := Y) (ofDrawing p)) :=
  Proofs.PositionedRuntime.read_left_word plan p

end Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap.LeftPlacement

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap

open Presentation

universe u v
variable {G : EffectfulPolygraph.{u,v}} {X Y : FixedRuntimeCap G}

/-- A single geometric step adds its incoming and outgoing crossing rows
and carries the idle strand through each of the active drawing's rows. -/
theorem placeLeftDrawing_cells (x : G.Obj) (idle lower upper : FixedCap (signature G))
    (idleTypes : idle.types = [some x]) (lowerTypes : lower.types = values X.word)
    (upperTypes : upper.types = values Y.word) {A B : FixedCap (signature G)}
    (input : A.types = none :: some x :: values X.word)
    (output : B.types = none :: some x :: values Y.word)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    (placeLeftDrawing x idle lower upper idleTypes lowerTypes upperTypes input output p).readSheet.cells =
      [.inr (.moveRight x) :: (values X.word).map Sum.inl] ++
        p.readSheet.cells.map (.inl (some x) :: ·) ++
        [.inr (.moveLeft x) :: (values Y.word).map Sum.inl] :=
  Proofs.PositionedRuntime.place_left_cells x idle lower upper idleTypes lowerTypes upperTypes input output p

end Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap

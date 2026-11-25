module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.Through

public noncomputable section

/-!
# Figure 10 left whiskering with active value ports

The active drawing uses the runtime as its first contact on each cap.
The lower box reads the rightward crossing and the upper box reads the
leftward crossing. Each box passes its own trailing value word, so the
input and output value words can differ. The comparison is in the runtime
presentation of Lemma 3.11 in Román and Sobociński, arXiv:2305.06075v5.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory Presentation
open scoped MonoidalCategory

universe u v
variable {G : EffectfulPolygraph.{u,v}}

namespace FixedCap

/-- When both chosen contacts agree with the placed through coordinate, one
wire joins their slots and stays at that coordinate across the full layer. -/
theorem binaryLayer_straight_through {O : Type u} {S : Signature.{u,v} O}
    (e : S.Edge) {a b c d : O} (src : S.source e = [a, b]) (tgt : S.target e = [c, d])
    (Q : FixedCap S) {A B : FixedCap S} (input : A.types = [a, b] ++ Q.types)
    (output : [c, d] ++ Q.types = B.types) (j : Fin Q.profile.size)
    (bottom : A.profile.x (binaryThroughSlot a b Q input j) = ActiveStrip.right.place (Q.profile.x j))
    (top : B.profile.x (binaryThroughSlot c d Q output.symm j) = ActiveStrip.right.place (Q.profile.x j)) :
    let p := binaryLayer e src tgt Q input output
    let w := (p.input (binaryThroughSlot a b Q input j)).val
    w = (p.output (binaryThroughSlot c d Q output.symm j)).val ∧
      ∀ y, p.drawing.x w y = ActiveStrip.right.place (Q.profile.x j) :=
  Proofs.PositionedRuntime.binary_through e src tgt Q input output j bottom top

/-- Read the geometric box and its right through strands between the chosen cuts. -/
theorem runtimeSweep_binaryLayer (e : Edge G) {a b c d : Presentation.Wire G.Obj}
    (src : (signature G).source e = [a, b]) (tgt : (signature G).target e = [c, d])
    (Q : FixedCap (signature G)) {A B : FixedCap (signature G)}
    (input : A.types = [a, b] ++ Q.types) (output : [c, d] ++ Q.types = B.types) :
    (runtimeSweep G).map (ofDrawing (binaryLayer e src tgt Q input output)) =
      eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G))
        (input.trans (congrArg (· ++ Q.types) src.symm))) ≫
        (Diagram.Presented.ofTerm (Diagram.gen (S := signature G) e) ▷ (runtimeSweep G).obj Q) ≫
        eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G))
          ((congrArg (· ++ Q.types) tgt).trans output)) :=
  Proofs.PositionedRuntime.LeftPorts.read_layer e src tgt Q input output

end FixedCap

namespace FixedRuntimeCap

/-- Figure 10 with one added left value. The active source and target may
have different value words. The two crossing layers are read from geometry,
with the corresponding active value words passing on their right. -/
theorem toComputations_placeLeft {X Y : FixedRuntimeCap G} (x : G.Obj) (P Q R : FixedCap (signature G))
    (idle : P.types = [some x]) (bottom : Q.types = values X.word) (top : R.types = values Y.word)
    {A B : FixedCap (signature G)} (input : A.types = none :: some x :: values X.word)
    (output : B.types = none :: some x :: values Y.word)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    (toComputations G).map (X := X.leftBoundary x A input) (Y := Y.leftBoundary x B output)
      (ofDrawing (placeLeftDrawing x P Q R idle bottom top input output p)) =
    (Computations.whiskerLeft (Computations.mk [x])).map
      ((toComputations G).map (ofDrawing p)) :=
  Proofs.PositionedRuntime.LeftPorts.place_left x P Q R idle bottom top input output p

end FixedRuntimeCap
end Silmaril.RuntimeWires.ProgressiveGraph

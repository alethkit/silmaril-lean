module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.BinaryBox.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms

public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph

open CategoryTheory Presentation

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

namespace FixedCap

/-- The ordered prefix of a padded binary box, followed by its through contacts. -/
theorem binary_beside_types (a b : O) (Q : FixedCap S) :
    ((binaryCap S a b).beside Q).types = [a, b] ++ Q.types :=
  (beside_labels _ _).trans (congrArg (· ++ Q.types) (binaryCap_types S a b))

/-- The slot of a through-wire at a cut of the padded binary layer. -/
def binaryThroughSlot (a b : O) (Q : FixedCap S) {A : FixedCap S}
    (word : A.types = [a, b] ++ Q.types) (j : Fin Q.profile.size) : Fin A.profile.size :=
  (recoordinationSlots (word.trans (binary_beside_types a b Q).symm)).symm
    ((ActiveStrip.left.capSlots (binaryCap S a b) Q).symm (.inr j))

theorem binaryThroughSlot_val (a b : O) (Q : FixedCap S) {A : FixedCap S}
    (word : A.types = [a, b] ++ Q.types) (j : Fin Q.profile.size) :
    (binaryThroughSlot a b Q word j).val = 2 + j.val := by
  change ((ActiveStrip.left.capSlots (binaryCap S a b) Q).symm (.inr j)).val = _
  exact ActiveStrip.left.idle_slot_val (binaryCap S a b) Q j

/-- Place a binary generator to the left of straight through strands. The two
vertex-free interpolations connect the placed box to independently chosen
ordered cuts. The through strands bypass the vertex in the idle strip. -/
def binaryLayer (e : S.Edge) {a b c d : O} (src : S.source e = [a, b])
    (tgt : S.target e = [c, d]) (Q : FixedCap S) {A B : FixedCap S}
    (input : A.types = [a, b] ++ Q.types) (output : [c, d] ++ Q.types = B.types) :
    FixedDrawing S A.profile B.profile :=
  let enter := interpolationDrawing (input.trans (binary_beside_types a b Q).symm)
  let leave := interpolationDrawing ((binary_beside_types c d Q).trans output)
  enter.thenDo ((ActiveStrip.left.placeDrawing
    (a := binaryCap S a b) (b := binaryCap S c d) (binaryBox e src tgt) Q).thenDo leave)

end FixedCap

namespace FixedRuntimeCap

variable {G : EffectfulPolygraph.{u,v}} {X Y : FixedRuntimeCap G}

/-- A new outer cut for single-value left whiskering, with independently
specified coordinates and the runtime still in the first slot. -/
@[expose] def leftBoundary (X : FixedRuntimeCap G) (x : G.Obj) (A : FixedCap (signature G))
    (types : A.types = none :: some x :: values X.word) : FixedRuntimeCap G :=
  ⟨A, x :: X.word, types⟩

/-- The actual cut of the placed drawing has the idle value before the runtime. -/
theorem leftPlaced_types (X : FixedRuntimeCap G) (x : G.Obj) (P : FixedCap (signature G))
    (idle : P.types = [some x]) : (P.beside X.cap).types = some x :: none :: values X.word :=
  (FixedCap.beside_labels _ _).trans (congrArg₂ (· ++ ·) idle X.types)

/-- The lower crossing layer moves the runtime past the added value while the
remaining value wires bypass the vertex. -/
def enterLeft (X : FixedRuntimeCap G) (x : G.Obj) (P Q : FixedCap (signature G))
    (idle : P.types = [some x]) (through : Q.types = values X.word)
    {A : FixedCap (signature G)} (types : A.types = none :: some x :: values X.word) :
    FixedDrawing (signature G) A.profile (P.beside X.cap).profile :=
  FixedCap.binaryLayer (Edge.moveRight (G := G) x) rfl rfl Q
    (types.trans (congrArg ([none, some x] ++ ·) through.symm))
    ((congrArg ([some x, none] ++ ·) through).trans (X.leftPlaced_types x P idle).symm)

/-- The upper crossing has the opposite orientation and uses the target
value contacts as its through strands. -/
def leaveLeft (Y : FixedRuntimeCap G) (x : G.Obj) (P Q : FixedCap (signature G))
    (idle : P.types = [some x]) (through : Q.types = values Y.word)
    {B : FixedCap (signature G)} (types : B.types = none :: some x :: values Y.word) :
    FixedDrawing (signature G) (P.beside Y.cap).profile B.profile :=
  FixedCap.binaryLayer (Edge.moveLeft (G := G) x) rfl rfl Q
    ((Y.leftPlaced_types x P idle).trans (congrArg ([some x, none] ++ ·) through.symm))
    ((congrArg ([none, some x] ++ ·) through).trans types.symm)

/-- The decorated representative uses actual horizontal placement and collared
vertical gluing to the two geometric crossing layers. -/
def placeLeftDrawing (x : G.Obj) (P Q R : FixedCap (signature G))
    (idle : P.types = [some x]) (bottom : Q.types = values X.word) (top : R.types = values Y.word)
    {A B : FixedCap (signature G)} (input : A.types = none :: some x :: values X.word)
    (output : B.types = none :: some x :: values Y.word)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    FixedDrawing (signature G) A.profile B.profile :=
  (X.enterLeft x P Q idle bottom input).thenDo
    ((ActiveStrip.right.placeDrawing (a := X.cap) (b := Y.cap) p P).thenDo
      (Y.leaveLeft x P R idle top output))

end FixedRuntimeCap
end Silmaril.RuntimeWires.ProgressiveGraph

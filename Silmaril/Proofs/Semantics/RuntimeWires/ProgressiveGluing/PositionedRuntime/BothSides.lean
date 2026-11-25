module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.BothSides.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.BothSides.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Defs

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.PositionedRuntime

open CategoryTheory Presentation ProgressiveGraph FixedRuntimeCap
open scoped MonoidalCategory

universe u v
variable {G : EffectfulPolygraph.{u,v}} {X Y : FixedRuntimeCap G} {L R : List G.Obj}

theorem read_right_drawing (P : FixedCap (signature G)) (types : P.types = values R)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    (toComputations G).map (X := X.padRight P types) (Y := Y.padRight P types)
      (ofDrawing (padRightDrawing P types p)) =
    (Computations.whiskerRight (Computations.mk R)).map
      ((toComputations G).map (X := X) (Y := Y) (ofDrawing p)) := by
  have h : (show X.cap ⟶ Y.cap from FixedCap.ofDrawing p) ▷ P =
      (show (X.padRight P types).cap ⟶ (Y.padRight P types).cap from
        FixedCap.ofDrawing (padRightDrawing P types p)) :=
    ActiveStrip.left.whisker_drawings (a := X.cap) (b := Y.cap) P p
  exact (congrArg ((toComputations G).map (X := X.padRight P types) (Y := Y.padRight P types)) h.symm).trans
    (toComputations_padRight P types (ofDrawing p))

theorem right_cells_at (P : FixedCap (signature G)) (types : P.types = values R)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile)
    (s : p.drawing.LayerSweep) (t : (padRightDrawing P types p).drawing.LayerSweep) :
    ((padRightDrawing P types p).readSheetAt t).cells =
      (p.readSheetAt s).cells.map (· ++ (values R).map Sum.inl) := by
  have h := ActiveStrip.readSheetAt_left (a := X.cap) (b := Y.cap) p P s t
  change ((ActiveStrip.left.placeDrawing (a := X.cap) (b := Y.cap) p P).readSheetAt t).cells = _
  erw [h, Sliced.Sheet.cells_reindex, Sliced.Sheet.cells_padRight, types]

variable {A B C D : FixedCap (signature G)}
variable {P Q : FixedCap (signature G)} {pTypes : P.types = values R} {qTypes : Q.types = values R}

theorem mixed_types (left : LeftPlacement X Y L A B)
    (right : LeftPlacement (X.padRight Q qTypes) (Y.padRight Q qTypes) L C D) :
    ((left.source.padRight P pTypes).cap.types = right.source.cap.types) ∧
      ((left.target.padRight P pTypes).cap.types = right.target.cap.types) := by
  have capWord (U V : FixedRuntimeCap G) (word : U.word = V.word) : U.cap.types = V.cap.types :=
    U.types.trans ((congrArg (fun W => none :: values W) word).trans V.types.symm)
  exact ⟨capWord _ _ (List.append_assoc L X.word R), capWord _ _ (List.append_assoc L Y.word R)⟩

theorem read_mixed (left : LeftPlacement X Y L A B)
    (right : LeftPlacement (X.padRight Q qTypes) (Y.padRight Q qTypes) L C D)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    (toComputations G).map (X := left.source.padRight P pTypes) (Y := left.target.padRight P pTypes)
      (ofDrawing (padRightDrawing P pTypes (left.drawing p))) ≫
        eqToHom (Computations.concat_assoc (Computations.mk L) Y.computation (Computations.mk R)) =
    eqToHom (Computations.concat_assoc (Computations.mk L) X.computation (Computations.mk R)) ≫
      (toComputations G).map (X := right.source) (Y := right.target)
        (ofDrawing (right.drawing (padRightDrawing Q qTypes p))) := by
  erw [read_right_drawing (X := left.source) (Y := left.target) P pTypes (left.drawing p),
    left.toComputations_drawing p, right.toComputations_drawing (padRightDrawing Q qTypes p),
    read_right_drawing (X := X) (Y := Y) Q qTypes p]
  exact PremonoidalCategory.associator_naturality_middle (Computations.mk L)
    ((toComputations G).map (X := X) (Y := Y) (ofDrawing p)) (Computations.mk R)

end Silmaril.RuntimeWires.Proofs.PositionedRuntime

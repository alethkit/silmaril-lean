module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftWord.Defs

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.PositionedRuntime

open CategoryTheory Presentation ProgressiveGraph FixedRuntimeCap

universe u v
variable {G : EffectfulPolygraph.{u,v}} {X Y : FixedRuntimeCap G}
variable {w : List G.Obj} {A B : FixedCap (signature G)}

theorem read_left_word (plan : LeftPlacement X Y w A B)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    (toComputations G).map (X := plan.source) (Y := plan.target) (ofDrawing (plan.drawing p)) =
      (Computations.whiskerLeft (Computations.mk w)).map
        ((toComputations G).map (X := X) (Y := Y) (ofDrawing p)) := by
  induction plan with
  | nil =>
    let f := (toComputations G).map (X := X) (Y := Y) (ofDrawing p)
    change f = _
    exact (Computations.whiskerLeft_nil f).symm
  | cons tail x idle lower upper idleTypes lowerTypes upperTypes input output ih =>
    refine (toComputations_placeLeft (X := tail.source) (Y := tail.target) x idle lower upper
      idleTypes lowerTypes upperTypes input output (tail.drawing p)).trans ?_
    rw [ih, Computations.whiskerLeft_cons]
    rfl

end Silmaril.RuntimeWires.Proofs.PositionedRuntime

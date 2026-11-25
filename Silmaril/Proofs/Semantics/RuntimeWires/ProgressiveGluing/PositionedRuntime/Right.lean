module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.Padding

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.PositionedRuntime

open CategoryTheory Presentation ProgressiveGraph
open scoped MonoidalCategory

universe u v
variable {G : EffectfulPolygraph.{u,v}}

private theorem whisker_transport {A B A' B' P P' : Runtime G}
    (f : A ⟶ B) (ha : A = A') (hb : B = B') (hp : P = P') :
    (eqToHom ha.symm ≫ f ≫ eqToHom hb) ▷ P' =
      eqToHom (congrArg₂ (· ⊗ ·) ha hp).symm ≫ f ▷ P ≫ eqToHom (congrArg₂ (· ⊗ ·) hb hp) := by
  subst A' B' P'
  simp

theorem pad_right {X Y : FixedRuntimeCap G} (P : FixedCap (signature G)) {W : List G.Obj}
    (types : P.types = values W) (f : X ⟶ Y) :
    (FixedRuntimeCap.toComputations G).map (X := X.padRight P types) (Y := Y.padRight P types)
      (show X.padRight P types ⟶ Y.padRight P types from (show X.cap ⟶ Y.cap from f) ▷ P) =
    (Computations.whiskerRight (Computations.mk W)).map ((FixedRuntimeCap.toComputations G).map f) := by
  let F := FixedCap.runtimeSweep G
  let m := F.map (show X.cap ⟶ Y.cap from f)
  let X' := X.padRight P types
  let Y' := Y.padRight P types
  let V := valueWord (G := G) W
  let W' : Computations G := ⟨W⟩
  let mk := Diagram.Presented.mk (S := signature G) (E := Relations G)
  have a : F.obj X.cap = X.computation.boundary := congrArg mk X.types
  have b : F.obj Y.cap = Y.computation.boundary := congrArg mk Y.types
  have p : F.obj P = V := congrArg mk types
  have a' : F.obj X'.cap = X'.computation.boundary := congrArg mk X'.types
  have b' : F.obj Y'.cap = Y'.computation.boundary := congrArg mk Y'.types
  have ma : F.obj X'.cap = F.obj X.cap ⊗ F.obj P := congrArg mk (FixedCap.beside_labels X.cap P)
  have mb : F.obj Y'.cap = F.obj Y.cap ⊗ F.obj P := congrArg mk (FixedCap.beside_labels Y.cap P)
  have ra : X'.computation.boundary = X.computation.boundary ⊗ V :=
    a'.symm.trans (ma.trans (congrArg₂ (· ⊗ ·) a p))
  have rb : Y'.computation.boundary = Y.computation.boundary ⊗ V :=
    b'.symm.trans (mb.trans (congrArg₂ (· ⊗ ·) b p))
  change eqToHom a'.symm ≫ F.map ((show X.cap ⟶ Y.cap from f) ▷ P) ≫ eqToHom b' =
    (X.computation.splitRight W').hom ≫ (eqToHom a.symm ≫ m ≫ eqToHom b) ▷ V ≫
      (Y.computation.splitRight W').inv
  erw [map_right, Computations.splitRight_eqToIso X.computation W' ra,
    Computations.splitRight_eqToIso Y.computation W' rb]
  change eqToHom a'.symm ≫ (eqToHom ma ≫ m ▷ F.obj P ≫ eqToHom mb.symm) ≫ eqToHom b' =
    eqToHom ra ≫ (eqToHom a.symm ≫ m ≫ eqToHom b) ▷ V ≫ eqToHom rb.symm
  rw [whisker_transport m a b p]
  simp only [Category.assoc]
  repeat erw [eqToHom_trans_assoc, eqToHom_trans]

end Silmaril.RuntimeWires.Proofs.PositionedRuntime

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

private theorem whisker_transport_left {A B A' B' P P' : Runtime G}
    (f : A ⟶ B) (ha : A = A') (hb : B = B') (hp : P = P') :
    P' ◁ (eqToHom ha.symm ≫ f ≫ eqToHom hb) =
      eqToHom (congrArg₂ (· ⊗ ·) hp ha).symm ≫ P ◁ f ≫ eqToHom (congrArg₂ (· ⊗ ·) hp hb) := by
  subst A' B' P'
  simp

theorem left_scalar (x : G.Obj) {A B E H : FixedCap (signature G)} (P : FixedCap (signature G))
    (hp : P.types = [some x]) (ha : A.types = [none]) (hb : B.types = [none])
    (he : E.types = [none, some x]) (hh : H.types = [none, some x]) (f : A ⟶ B)
    (enter : IsolatedRuntimeGenerator (.moveRight x) E (P.beside A))
    (leave : IsolatedRuntimeGenerator (.moveLeft x) (P.beside B) H) :
    (FixedRuntimeCap.toComputations G).map (X := ⟨E, [x], he⟩) (Y := ⟨H, [x], hh⟩)
      (show (⟨E, [x], he⟩ : FixedRuntimeCap G) ⟶ ⟨H, [x], hh⟩ from
        show E ⟶ H from
          FixedCap.ofDrawing (a := E) (b := P.beside A) enter.drawing ≫ P ◁ f ≫
            FixedCap.ofDrawing (a := P.beside B) (b := H) leave.drawing) =
    (Computations.whiskerLeft (Computations.mk [x])).map
      ((FixedRuntimeCap.toComputations G).map (X := ⟨A, [], ha⟩) (Y := ⟨B, [], hb⟩) f) := by
  let F := FixedCap.runtimeSweep G
  let mk := Diagram.Presented.mk (S := signature G) (E := Relations G)
  let I := valueWord (G := G) [x]
  let R := runtime G
  let u : E ⟶ P.beside A := FixedCap.ofDrawing enter.drawing
  let v : P.beside B ⟶ H := FixedCap.ofDrawing leave.drawing
  have a : F.obj A = R := congrArg mk ha
  have b : F.obj B = R := congrArg mk hb
  have i : F.obj P = I := congrArg mk hp
  have e : F.obj E = R ⊗ I := congrArg mk he
  have h : F.obj H = R ⊗ I := congrArg mk hh
  have pa : (P.beside A).types = [some x, none] := (FixedCap.beside_labels P A).trans (by
    change P.types ++ A.types = _
    rw [hp, ha]
    rfl)
  have pb : (P.beside B).types = [some x, none] := (FixedCap.beside_labels P B).trans (by
    change P.types ++ B.types = _
    rw [hp, hb]
    rfl)
  have re := FixedCap.runtimeSweep_generator (A := E) (B := P.beside A) (.moveRight x)
    enter.drawing enter.vertex enter.only enter.label enter.noThrough he pa.symm
  have rl := FixedCap.runtimeSweep_generator (A := P.beside B) (B := H) (.moveLeft x)
    leave.drawing leave.vertex leave.only leave.label leave.noThrough pb hh.symm
  let X : Computations G := ⟨[x]⟩
  let Y : Computations G := ⟨[]⟩
  change eqToHom e.symm ≫ F.map (u ≫ P ◁ f ≫ v) ≫ eqToHom h =
    (X.splitLeft Y).hom ≫ I ◁ (eqToHom a.symm ≫ F.map f ≫ eqToHom b) ≫ (X.splitLeft Y).inv
  erw [F.map_comp, F.map_comp, re, map_left, rl, Computations.splitLeft_singleton_empty]
  erw [whisker_transport_left (F.map f) a b i]
  repeat erw [Category.assoc]
  repeat first | erw [eqToHom_trans_assoc] | erw [eqToHom_trans]
  repeat first | erw [eqToHom_refl] | erw [Category.id_comp] | erw [Category.comp_id]
  rfl

end Silmaril.RuntimeWires.Proofs.PositionedRuntime

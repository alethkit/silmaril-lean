module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Defs

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.PositionedRuntime.LeftPorts

open CategoryTheory Presentation ProgressiveGraph
open scoped MonoidalCategory

universe u v
variable {G : EffectfulPolygraph.{u,v}}

abbrev F (G : EffectfulPolygraph.{u,v}) := FixedCap.runtimeSweep G
abbrev mk (G : EffectfulPolygraph.{u,v}) :=
  Diagram.Presented.mk (S := signature G) (E := Relations G)

/-- Inline the existing vertex-free readout through the two quotient maps. -/
private theorem read_interpolation {A B : FixedCap (signature G)} (h : A.types = B.types) :
    (F G).map (FixedCap.ofDrawing (a := A) (b := B) (FixedCap.interpolationDrawing h)) =
      eqToHom (congrArg (mk G) h) := by
  let T := Sliced.Presented.toTerms (signature G) ⋙ FixedRuntimeCap.termToRuntime G
  change T.map ((FixedCap.toSliced (signature G)).map (FixedCap.recoordinate h)) = _
  rw [FixedCap.toSliced_recoordinate, Sliced.Presented.ofSheet_reindex]
  erw [T.map_comp, T.map_comp, eqToHom_map, eqToHom_map]
  change _ ≫ T.map (𝟙 (⟨A.types⟩ : Sliced.Presented (signature G))) ≫ _ = _
  erw [T.map_id, eqToHom_refl, Category.id_comp, Category.id_comp]
  rfl

private theorem right_transport {A B A' B' P : Runtime G} (f : A ⟶ B)
    (a : A' = A) (b : B = B') : (eqToHom a ≫ f ≫ eqToHom b) ▷ P =
      eqToHom (congrArg (· ⊗ P) a) ≫ f ▷ P ≫ eqToHom (congrArg (· ⊗ P) b) := by
  subst A' B'
  simp

private theorem left_transport {A B A' B' P P' : Runtime G} (f : A ⟶ B)
    (a : A = A') (b : B = B') (p : P = P') :
    P' ◁ (eqToHom a.symm ≫ f ≫ eqToHom b) =
      eqToHom (congrArg₂ (· ⊗ ·) p a).symm ≫ P ◁ f ≫ eqToHom (congrArg₂ (· ⊗ ·) p b) := by
  subst A' B' P'
  simp

/-- The binary box is an independently read generator with no through strand. -/
private theorem read_box (e : Edge G) {a b c d : Presentation.Wire G.Obj}
    (src : (signature G).source e = [a, b]) (tgt : (signature G).target e = [c, d]) :
    (F G).map (FixedCap.ofDrawing (a := binaryCap (signature G) a b)
      (b := binaryCap (signature G) c d) (binaryBox (S := signature G) e src tgt)) =
      eqToHom (congrArg (mk G) ((binaryCap_types _ a b).trans src.symm)) ≫
        Diagram.Presented.ofTerm (Diagram.gen (S := signature G) e) ≫
        eqToHom (congrArg (mk G) (tgt.trans (binaryCap_types _ c d).symm)) := by
  let p := binaryBox (S := signature G) e src tgt
  have count : p.vertices = 1 := binaryBox_vertices (S := signature G) e src tgt
  let v : Fin p.vertices := (0 : Fin 1).cast count.symm
  have only (j : Fin p.vertices) : j = v := (finCongr count).injective (Subsingleton.elim _ _)
  exact FixedCap.runtimeSweep_generator e p v only (binaryBox_generator (S := signature G) e src tgt v)
    (fun i => binaryBox_noThrough (S := signature G) e src tgt i v)
    ((binaryCap_types _ a b).trans src.symm) (tgt.trans (binaryCap_types _ c d).symm)

/-- Read a generator with actual right through strands between two specified cuts. -/
theorem read_layer (e : Edge G) {a b c d : Presentation.Wire G.Obj}
    (src : (signature G).source e = [a, b]) (tgt : (signature G).target e = [c, d])
    (Q : FixedCap (signature G)) {A B : FixedCap (signature G)}
    (input : A.types = [a, b] ++ Q.types) (output : [c, d] ++ Q.types = B.types) :
    (F G).map (FixedCap.ofDrawing (FixedCap.binaryLayer e src tgt Q input output)) =
      eqToHom (congrArg (mk G) (input.trans (congrArg (· ++ Q.types) src.symm))) ≫
        (Diagram.Presented.ofTerm (Diagram.gen (S := signature G) e) ▷ (F G).obj Q) ≫
        eqToHom (congrArg (mk G) ((congrArg (· ++ Q.types) tgt).trans output)) := by
  let S := signature G
  let L := binaryCap S a b
  let R := binaryCap S c d
  let p := binaryBox (S := signature G) e src tgt
  let i := input.trans (FixedCap.binary_beside_types a b Q).symm
  let o := (FixedCap.binary_beside_types c d Q).trans output
  change (F G).map (FixedCap.ofDrawing (a := A) (b := B)
    ((FixedCap.interpolationDrawing (a := A) (b := L.beside Q) i).thenDo
      ((ActiveStrip.left.placeDrawing (a := L) (b := R) p Q).thenDo
        (FixedCap.interpolationDrawing (a := R.beside Q) (b := B) o)))) = _
  erw [← FixedCap.comp_drawings (a := A) (b := L.beside Q) (c := B),
    ← FixedCap.comp_drawings (a := L.beside Q) (b := R.beside Q) (c := B)]
  have placed : FixedCap.ofDrawing (a := L.beside Q) (b := R.beside Q)
      (ActiveStrip.left.placeDrawing (a := L) (b := R) p Q) =
      (FixedCap.ofDrawing (a := L) (b := R) p) ▷ Q :=
    (ActiveStrip.left.whisker_drawings (a := L) (b := R) Q p).symm
  erw [(F G).map_comp, (F G).map_comp, read_interpolation i, read_interpolation o,
    placed, FixedCap.runtimeSweep_padRight, read_box e src tgt, right_transport]
  repeat erw [Category.assoc]
  repeat first | erw [eqToHom_trans_assoc] | erw [eqToHom_trans]
  rfl

private theorem whisker_tracks {A B P P' : Runtime G} (f : A ⟶ B) (h : P = P') :
    f ▷ P = eqToHom (congrArg (A ⊗ ·) h) ≫ f ▷ P' ≫ eqToHom (congrArg (B ⊗ ·) h.symm) := by
  subst P'
  simp

theorem place_left {X Y : FixedRuntimeCap G} (x : G.Obj) (P Q R : FixedCap (signature G))
    (idle : P.types = [some x]) (bottom : Q.types = values X.word) (top : R.types = values Y.word)
    {A B : FixedCap (signature G)} (input : A.types = none :: some x :: values X.word)
    (output : B.types = none :: some x :: values Y.word)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    (FixedRuntimeCap.toComputations G).map (X := X.leftBoundary x A input) (Y := Y.leftBoundary x B output)
      (FixedRuntimeCap.ofDrawing (FixedRuntimeCap.placeLeftDrawing x P Q R idle bottom top input output p)) =
    (Computations.whiskerLeft (Computations.mk [x])).map
      ((FixedRuntimeCap.toComputations G).map (FixedRuntimeCap.ofDrawing p)) := by
  let U := P.beside X.cap
  let V := P.beside Y.cap
  let enter := X.enterLeft x P Q idle bottom input
  let leave := Y.leaveLeft x P R idle top output
  let f : X.cap ⟶ Y.cap := FixedCap.ofDrawing p
  let I := valueWord (G := G) [x]
  let L : Computations G := ⟨[x]⟩
  have placed : FixedCap.ofDrawing (a := U) (b := V)
      (ActiveStrip.right.placeDrawing (a := X.cap) (b := Y.cap) p P) = P ◁ f :=
    (ActiveStrip.right.whisker_drawings (a := X.cap) (b := Y.cap) P p).symm
  have re := read_layer (.moveRight x) rfl rfl Q
    (A := A) (B := U)
    (input.trans (congrArg ([none, some x] ++ ·) bottom.symm))
    ((congrArg ([some x, none] ++ ·) bottom).trans (X.leftPlaced_types x P idle).symm)
  have rl := read_layer (.moveLeft x) rfl rfl R
    (A := V) (B := B)
    ((Y.leftPlaced_types x P idle).trans (congrArg ([some x, none] ++ ·) top.symm))
    ((congrArg ([none, some x] ++ ·) top).trans output.symm)
  change eqToHom (congrArg (mk G) input.symm) ≫ (F G).map
    (FixedCap.ofDrawing (a := A) (b := B)
      (enter.thenDo ((ActiveStrip.right.placeDrawing (a := X.cap) (b := Y.cap) p P).thenDo leave))) ≫
    eqToHom (congrArg (mk G) output) =
    (L.splitLeft X.computation).hom ≫ I ◁
      (eqToHom (congrArg (mk G) X.types.symm) ≫ (F G).map f ≫ eqToHom (congrArg (mk G) Y.types)) ≫
      (L.splitLeft Y.computation).inv
  erw [← FixedCap.comp_drawings (a := A) (b := U) (c := B),
    ← FixedCap.comp_drawings (a := U) (b := V) (c := B), placed,
    (F G).map_comp, (F G).map_comp, re, FixedCap.runtimeSweep_padLeft, rl,
    Computations.splitLeft_singleton_hom, Computations.splitLeft_singleton_inv]
  erw [whisker_tracks _ (congrArg (mk G) bottom), whisker_tracks _ (congrArg (mk G) top),
    left_transport ((F G).map f) (congrArg (mk G) X.types) (congrArg (mk G) Y.types)
      (congrArg (mk G) idle)]
  repeat erw [Category.assoc]
  repeat first | erw [eqToHom_trans_assoc] | erw [eqToHom_trans]
  repeat first | erw [eqToHom_refl] | erw [Category.id_comp] | erw [Category.comp_id]
  rfl

end Silmaril.RuntimeWires.Proofs.PositionedRuntime.LeftPorts

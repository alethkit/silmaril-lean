module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.RuntimeReadout.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.RuntimeReadout.Generator

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.RuntimeReadout

open CategoryTheory Presentation ProgressiveGraph FixedRuntimeCap
open Sliced (SeamHom Sheet)

universe u v
variable {G : EffectfulPolygraph.{u,v}} {X Y : FixedRuntimeCap G}

theorem naturality (f : X ⟶ Y) :
    (toRuntime G).map f ≫ Y.boundaryIso.hom =
      X.boundaryIso.hom ≫ ((toComputations G) ⋙ Computations.inRuntime G).map f := by
  change _ = X.boundaryIso.hom ≫ (X.boundaryIso.inv ≫ _ ≫ Y.boundaryIso.hom)
  rw [X.boundaryIso.hom_inv_id_assoc]

private abbrev sliceRuntime (G : EffectfulPolygraph.{u,v}) :=
  Sliced.Presented.toTerms (signature G) ⋙ termToRuntime G

private theorem map_generator (e : Edge G) :
    (sliceRuntime G).map (SeamHom.ofSheet (Sheet.generator (S := signature G) e) :
        (⟨(signature G).source e⟩ : Sliced.Presented (signature G)) ⟶ ⟨(signature G).target e⟩) =
      Diagram.Presented.ofTerm (Diagram.gen (S := signature G) e) := by
  change (termToRuntime G).map ((Sliced.Presented.toTerms (signature G)).map _) = _
  rw [Sliced.Presented.toTerms_generator]
  rfl

private theorem map_transported_generator (e : Edge G) {A B : List (Presentation.Wire G.Obj)}
    (input : A = (signature G).source e) (output : (signature G).target e = B) :
    (sliceRuntime G).map (SeamHom.ofSheet ((Sheet.generator (S := signature G) e).reindex
      input.symm output) : (⟨A⟩ : Sliced.Presented (signature G)) ⟶ ⟨B⟩) =
      eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) input) ≫
        Diagram.Presented.ofTerm (Diagram.gen (S := signature G) e) ≫
        eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) output) := by
  cases input
  cases output
  exact (map_generator e).trans (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)

private theorem read_effect (e : G.effect.Edge)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) (vertex : Fin p.vertices)
    (only : ∀ j, j = vertex) (label : p.drawing.generator vertex = .effect e)
    (noThrough : ∀ w, ¬ p.drawing.crosses w (p.drawing.vertexHeight vertex))
    (input : X.cap.types = (signature G).source (.effect e))
    (output : (signature G).target (.effect e) = Y.cap.types) :
    (toRuntime G).map (ofDrawing p) =
      eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) input) ≫
        Diagram.Presented.ofTerm (Diagram.gen (S := signature G) (.effect e)) ≫
        eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) output) := by
  have cells := read_generator p vertex only p.drawing.layerSweep (.effect e) label noThrough input.symm output
  have sheet := (FixedCap.toSliced_drawings (a := X.cap) (b := Y.cap) p).trans
    (congrArg SeamHom.ofSheet cells)
  exact (congrArg (sliceRuntime G).map sheet).trans (map_transported_generator (.effect e) input output)

theorem map_effect (e : G.effect.Edge)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) (vertex : Fin p.vertices)
    (only : ∀ j, j = vertex) (label : p.drawing.generator vertex = .effect e)
    (noThrough : ∀ w, ¬ p.drawing.crosses w (p.drawing.vertexHeight vertex))
    (input : X.word = G.effect.source e) (output : G.effect.target e = Y.word) :
    (toComputations G).map (ofDrawing p) =
      eqToHom (congrArg (Computations.mk (G := G)) input) ≫
        Computations.effect e ≫ eqToHom (congrArg (Computations.mk (G := G)) output) := by
  let inWord : X.cap.types = (signature G).source (.effect e) :=
    X.types.trans (congrArg (fun A => none :: values A) input)
  let outWord : (signature G).target (.effect e) = Y.cap.types :=
    (congrArg (fun A => none :: values A) output).trans Y.types.symm
  change X.boundaryIso.inv ≫ (toRuntime G).map (ofDrawing p) ≫ Y.boundaryIso.hom = _
  rw [read_effect e p vertex only label noThrough inWord outWord]
  change eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) X.types.symm) ≫
    _ ≫ eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) Y.types) = _
  have hi := eqToHom_map (Computations.inRuntime G) (congrArg (Computations.mk (G := G)) input)
  have ho := eqToHom_map (Computations.inRuntime G) (congrArg (Computations.mk (G := G)) output)
  change _ =
    (Computations.inRuntime G).map (eqToHom (congrArg (Computations.mk (G := G)) input)) ≫
      (Computations.inRuntime G).map (Computations.effect e) ≫
      (Computations.inRuntime G).map (eqToHom (congrArg (Computations.mk (G := G)) output))
  rw [hi, ho]
  simp only [Category.assoc]
  rw [eqToHom_trans_assoc, eqToHom_trans]
  rfl

end Silmaril.RuntimeWires.Proofs.RuntimeReadout

module

public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms
public import Silmaril.SSA.RVSDG.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Coherence

/-! Signature, sentence and model coherence for the generated γ lowering. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG

open CategoryTheory
open RVSDG (Tuple)

universe u v w
variable {Data : Type u} {P Q R : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}

theorem mapSignature_id (P : Signature.{u, v} Data) :
    mapSignature (𝟙 P) = 𝟙 (signature P) :=
  Proofs.mapSignature_id P

theorem mapSignature_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    mapSignature (h ≫ k) = mapSignature h ≫ mapSignature k :=
  Proofs.mapSignature_comp h k

/-- The typed signature lift into the existing RVSDG signature category. -/
@[expose] def signatureFunctor (Data : Type u) :
    Signature.{u, v} Data ⥤ RVSDG.Institution.Signature.{u, max u v} (ValueSort Data) PEmpty.{u+1} where
  obj := signature
  map := mapSignature
  map_id := mapSignature_id
  map_comp := mapSignature_comp

/-- Relabelling the actual lowered numbered graph commutes with native relabelling. -/
theorem lower_map (h : P ⟶ Q) (g : Graph P.op inputs sigs out) :
    RVSDG.Institution.mapGraph (mapOpcode h) g.lower = (mapGraph h g).lower :=
  Proofs.lower_map h g

theorem lowerEquation_map (h : P ⟶ Q) (e : Equation P) :
    (lowerEquation e).map (mapOpcode h) = lowerEquation (e.map h) :=
  congrArg₂ (fun lhs rhs => (⟨dataPorts e.inputs, [.value e.out], _, _, lhs, rhs⟩ :
    RVSDG.Institution.Equation (signature Q).op)) (lower_map h e.lhs) (lower_map h e.rhs)

/-- The induced RVSDG model commutes with reduct, including Boolean dispatch. -/
theorem model_reduct (h : P ⟶ Q) (m : Model.{u, v, w} Q.op) :
    RVSDG.Institution.reduct (mapOpcode h) m.toRVSDG = (reduct h m).toRVSDG :=
  Proofs.model_reduct h m

/-- Running the generated graph returns the native denotation as a singleton tuple. -/
theorem lower_run (g : Graph P.op inputs sigs out) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) :
    g.lower.run m.toRVSDG input = .cons (g.denote m input) .nil :=
  Proofs.lower_run g m input

/-- At the induced model, the lowered equation holds exactly when the native equation does. -/
theorem satisfaction (e : Equation P) (m : Model.{u, v, w} P.op) :
    (lowerEquation e).Holds m.toRVSDG ↔ e.Holds m :=
  Proofs.satisfaction e m

/-- The satisfaction diagram in the existing rooms, starting from a native
target model and a source equation. -/
theorem satisfaction_map (h : P ⟶ Q) (e : Equation P) (m : Model.{u, v, w} Q.op) :
    (RVSDG.Institution.room (signature Q)).Sat (Discrete.mk m.toRVSDG)
      ((RVSDG.Institution.corridor (mapSignature h)).sen (lowerEquation e)) ↔
      (room P).Sat ((corridor h).mod.obj (Discrete.mk m)) e := by
  change ((lowerEquation e).map (mapOpcode h)).Holds m.toRVSDG ↔ e.Holds (reduct h m)
  rw [lowerEquation_map]
  exact (satisfaction (e.map h) m).trans (e.satisfaction h m)

end Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG

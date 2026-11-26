module

public import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Thms
import Silmaril.SSA.RVSDG.MLIR.Graph.Thms
import Silmaril.SSA.RVSDG.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Proofs

open CategoryTheory
open RVSDG (Origin extend)

variable {Data : Type} {P Q R : Diamond.Institution.Signature.{0, 0} Data}

theorem rvsdgMap_id (P : Diamond.Institution.Signature.{0, 0} Data) :
    rvsdgMap (𝟙 P) = 𝟙 (source P.op) := by
  change RVSDG.Institution.Signature.Hom.mk (P := source P.op) (Q := source P.op)
      (fun op => opcodeMap (𝟙 P) op) = RVSDG.Institution.Signature.Hom.mk (fun op => op)
  congr 1
  funext _ _ op
  cases op <;> rfl

theorem rvsdgMap_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    rvsdgMap (h ≫ k) = rvsdgMap h ≫ rvsdgMap k := by
  change RVSDG.Institution.Signature.Hom.mk (P := source P.op) (Q := source R.op)
      (fun op => opcodeMap (h ≫ k) op) =
    RVSDG.Institution.Signature.Hom.mk (fun op => opcodeMap k (opcodeMap h op))
  congr 1
  funext _ _ op
  cases op <;> rfl

private theorem map_lowerDataflow (h : P ⟶ Q) {args : List (Diamond.Ty Data)}
    {past sigs tail : List (List (Diamond.Ty Data))} {results : List (Diamond.Ty Data)}
    (dataflow : Dataflow P.op args past sigs)
    (rest : RVSDG.Term (Opcode P.op) args (extend past sigs) tail results) :
    RVSDG.Institution.mapTerm (opcodeMap h) (dataflow.lower rest) =
      (Diamond.Institution.mapDataflow h dataflow).lower (RVSDG.Institution.mapTerm (opcodeMap h) rest) := by
  induction dataflow with
  | nil => rfl
  | cons _ _ _ ih =>
    simp only [Diamond.Dataflow.lower, Diamond.Institution.mapDataflow, RVSDG.Institution.mapTerm]
    rw [ih rest]
    rfl

private theorem map_lowerPhi (h : P ⟶ Q) {args : List (Diamond.Ty Data)}
    {past : List (List (Diamond.Ty Data))} {out : ValueSort Data}
    (phi : Phi args past out) (predicate : Origin args past (.value .predicate)) :
    RVSDG.Institution.mapTerm (opcodeMap h) (phi.lower (Op := P.op) predicate) =
      phi.lower (Op := Q.op) predicate := by
  have arm_eq (i : Fin 2) :
      RVSDG.Institution.mapTerm (opcodeMap h) (arms (Op := P.op) (out := out) phi.merge i) =
        arms (Op := Q.op) (out := out) phi.merge i := by
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  simp only [Phi.lower, RVSDG.Institution.mapTerm, opcodeMap]
  congr 2
  exact funext arm_eq

theorem rvsdg_lower_map (h : P ⟶ Q) {inputs : List (ValueSort Data)}
    {sigs : List (List (Diamond.Ty Data))} {out : ValueSort Data} (g : Graph P.op inputs sigs out) :
    (Diamond.Institution.mapGraph h g).lower =
      RVSDG.Institution.mapGraph (opcodeMap h) g.lower := by
  rw [Graph.lower, Graph.lower, RVSDG.Institution.mapGraph_toGraph]
  simp only [Graph.lowerTerm, Diamond.Institution.mapGraph, map_lowerDataflow, map_lowerPhi]

theorem lower_map (h : P ⟶ Q) {inputs : List (ValueSort Data)}
    {sigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}
    (g : Graph P.op inputs sigs out) (i : Fin 1) :
    lower (Diamond.Institution.mapGraph h g) i = (lower g i).map (scopedMap h) := by
  simp only [lower, rvsdg_lower_map]
  exact RVSDG.MLIR.Graph.lower_map (rvsdgMap h) g.lower i

theorem translate_map (h : P ⟶ Q) (e : Diamond.Institution.Equation P) :
    translate (e.map h) = (translate e).map (scopedMap h) := by
  have lhs := funext (lower_map h e.lhs)
  have rhs := funext (lower_map h e.rhs)
  simp only [translate, Diamond.Institution.Equation.map, lowerEquation,
    Silmaril.MLIR.Institution.Equation.map]
  rw [lhs, rhs]
  rfl

private theorem rvsdg_model_reduct (h : P ⟶ Q) (m : Model.{0, 0, 0} Q.op) :
    RVSDG.Institution.reduct (opcodeMap h) m.toRVSDG =
      (Diamond.Institution.reduct h m).toRVSDG := by
  simp only [RVSDG.Institution.reduct, Diamond.Institution.reduct, Diamond.Model.toRVSDG]
  congr 1
  funext _ _ op input
  cases op with
  | pure => rfl
  | dispatch => cases input; rfl

theorem model_reduct (h : P ⟶ Q) (m : Model.{0, 0, 0} Q.op) :
    (model m).reduct (scopedMap h) = model (Diamond.Institution.reduct h m) := by
  rw [← RVSDG.MLIR.Graph.model_reduct (rvsdgMap h) m.toRVSDG]
  exact congrArg (RVSDG.MLIR.Graph.model (P := source P.op)) (rvsdg_model_reduct h m)

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Proofs

module

public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Thms
public import Silmaril.SSA.RVSDG.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Proofs

open CategoryTheory
open RVSDG (Origin Tuple extend)

universe u v w
variable {Data : Type u} {P Q R : Signature.{u, v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}

theorem mapSignature_id (P : Signature.{u, v} Data) :
    mapSignature (𝟙 P) = 𝟙 (signature P) := by
  change RVSDG.Institution.Signature.Hom.mk _ = RVSDG.Institution.Signature.Hom.mk _
  congr 1
  funext ins outs op
  cases op <;> rfl

theorem mapSignature_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    mapSignature (h ≫ k) = mapSignature h ≫ mapSignature k := by
  change RVSDG.Institution.Signature.Hom.mk _ = RVSDG.Institution.Signature.Hom.mk _
  congr 1
  funext ins outs op
  cases op <;> rfl

private theorem map_lowerDataflow (h : P ⟶ Q) {results : List (Ty Data)} {tail : List (List (Ty Data))}
    (flow : Dataflow P.op args past sigs)
    (rest : RVSDG.Term (Opcode P.op) args (extend past sigs) tail results) :
    RVSDG.Institution.mapTerm (mapOpcode h) (flow.lower rest) =
      (mapDataflow h flow).lower (RVSDG.Institution.mapTerm (mapOpcode h) rest) := by
  induction flow with
  | nil => rfl
  | cons op wires more ih =>
    simp only [Dataflow.lower, RVSDG.Institution.mapTerm, mapDataflow, mapOpcode]
    rw [ih rest]
    rfl

private theorem map_lowerPhi (h : P ⟶ Q) (phi : Phi args past out)
    (predicate : Origin args past (.value .predicate)) :
    RVSDG.Institution.mapTerm (mapOpcode h) (phi.lower predicate) =
      (phi.lower (Op := Q.op) predicate) := by
  simp only [Phi.lower, RVSDG.Institution.mapTerm, mapOpcode]
  congr 2
  funext armIndex
  exact Fin.cases rfl (fun _ => rfl) armIndex

theorem lower_map (h : P ⟶ Q) (g : Graph P.op inputs sigs out) :
    RVSDG.Institution.mapGraph (mapOpcode h) g.lower = (mapGraph h g).lower := by
  simp only [Graph.lower, RVSDG.Institution.mapGraph_toGraph, Graph.lowerTerm,
    map_lowerDataflow, map_lowerPhi, mapGraph]

set_option backward.isDefEq.respectTransparency false in
theorem model_reduct (h : P ⟶ Q) (m : Model.{u, v, w} Q.op) :
    RVSDG.Institution.reduct (mapOpcode h) m.toRVSDG = (reduct h m).toRVSDG := by
  unfold RVSDG.Institution.reduct reduct
  congr 1
  funext ins outs op input
  cases op with
  | pure => rfl
  | dispatch => cases input; rfl

theorem lower_run (g : Graph P.op inputs sigs out) (m : Model.{u, v, w} P.op)
    (input : Tuple (Val m.value) (dataPorts inputs)) :
    g.lower.run m.toRVSDG input = .cons (g.denote m input) .nil :=
  (g.lower_returns_iff m input _).mp ((g.returns_iff_denote m input _).mpr rfl)

set_option backward.isDefEq.respectTransparency false in
theorem satisfaction (e : Equation P) (m : Model.{u, v, w} P.op) :
    (lowerEquation e).Holds m.toRVSDG ↔ e.Holds m := by
  change (∀ input, e.lhs.lower.run m.toRVSDG input = e.rhs.lower.run m.toRVSDG input) ↔ _
  simp only [lower_run]
  constructor
  · intro h input
    exact congrArg (fun xs => xs.get .head) (h input)
  · intro h input
    exact congrArg (fun value => Tuple.cons value .nil) (h input)

end Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Proofs

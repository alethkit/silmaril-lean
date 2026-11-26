module

public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution.Proofs

open CategoryTheory
open RVSDG (Locals Tuple)

universe u v w

variable {Data : Type u} {P Q R : Signature.{u, v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}

theorem mapDataflow_id (t : Dataflow P.op args past sigs) :
    mapDataflow (𝟙 P) t = t := by
  induction t with
  | nil => rfl
  | cons _ _ _ ih => simp only [mapDataflow, ih]; rfl

theorem mapDataflow_comp (h : P ⟶ Q) (k : Q ⟶ R) (t : Dataflow P.op args past sigs) :
    mapDataflow (h ≫ k) t = mapDataflow k (mapDataflow h t) := by
  induction t with
  | nil => rfl
  | cons _ _ _ ih => simp only [mapDataflow, ih]; rfl

theorem mapGraph_id (g : Graph P.op inputs sigs out) : mapGraph (𝟙 P) g = g := by
  cases g
  simp only [mapGraph, mapDataflow_id]

theorem mapGraph_comp (h : P ⟶ Q) (k : Q ⟶ R) (g : Graph P.op inputs sigs out) :
    mapGraph (h ≫ k) g = mapGraph k (mapGraph h g) := by
  simp only [mapGraph, mapDataflow_comp]

theorem eval_mapDataflow (h : P ⟶ Q) (m : Model.{u, v, w} Q.op)
    (t : Dataflow P.op args past sigs) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) :
    (mapDataflow h t).eval m entry locals = t.eval (reduct h m) entry locals := by
  induction t with
  | nil => rfl
  | cons _ _ _ ih => exact ih _

theorem denote_mapGraph (h : P ⟶ Q) (m : Model.{u, v, w} Q.op)
    (g : Graph P.op inputs sigs out) (entry : Tuple (Val m.value) (dataPorts inputs)) :
    (mapGraph h g).denote m entry = g.denote (reduct h m) entry := by
  simp only [Diamond.Graph.denote, mapGraph]
  rw [eval_mapDataflow h m g.dataflow entry PUnit.unit]
  rfl

theorem equation_map_id (e : Equation P) : e.map (𝟙 P) = e := by
  cases e
  simp only [Equation.map, mapGraph_id]

theorem equation_map_comp (h : P ⟶ Q) (k : Q ⟶ R) (e : Equation P) :
    e.map (h ≫ k) = (e.map h).map k := by
  simp only [Equation.map, mapGraph_comp]

theorem satisfaction (h : P ⟶ Q) (e : Equation P) (m : Model.{u, v, w} Q.op) :
    (e.map h).Holds m ↔ e.Holds (reduct h m) := by
  change (∀ entry : Tuple (Val m.value) (dataPorts e.inputs),
    (mapGraph h e.lhs).denote m entry = (mapGraph h e.rhs).denote m entry) ↔ _
  simp only [denote_mapGraph, Equation.Holds]
  rfl

end Silmaril.SSA.SeaOfNodes.Diamond.Institution.Proofs

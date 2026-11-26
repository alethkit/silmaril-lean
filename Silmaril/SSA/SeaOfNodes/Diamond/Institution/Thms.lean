module

public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Institution.Reindex

/-! Change of signature for the native diamond equation institution. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Locals Tuple)

universe u v w

variable {Data : Type u} {P Q R : Signature.{u, v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}

@[simp] theorem mapGraph_id (g : Graph P.op inputs sigs out) : mapGraph (𝟙 P) g = g :=
  Proofs.mapGraph_id g

theorem mapGraph_comp (h : P ⟶ Q) (k : Q ⟶ R) (g : Graph P.op inputs sigs out) :
    mapGraph (h ≫ k) g = mapGraph k (mapGraph h g) :=
  Proofs.mapGraph_comp h k g

/-- The native dataflow evaluator gives the same locals after relabelling and reduction. -/
theorem eval_mapDataflow (h : P ⟶ Q) (m : Model.{u, v, w} Q.op)
    (t : Dataflow P.op args past sigs) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) :
    (mapDataflow h t).eval m entry locals = t.eval (reduct h m) entry locals :=
  Proofs.eval_mapDataflow h m t entry locals

/-- Denotation commutes with signature change at every typed input. -/
theorem denote_mapGraph (h : P ⟶ Q) (m : Model.{u, v, w} Q.op)
    (g : Graph P.op inputs sigs out) (entry : Tuple (Val m.value) (dataPorts inputs)) :
    (mapGraph h g).denote m entry = g.denote (reduct h m) entry :=
  Proofs.denote_mapGraph h m g entry

@[simp] theorem Equation.map_id (e : Equation P) : e.map (𝟙 P) = e :=
  Proofs.equation_map_id e

theorem Equation.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (e : Equation P) :
    e.map (h ≫ k) = (e.map h).map k :=
  Proofs.equation_map_comp h k e

@[simp] theorem reduct_id (m : Model.{u, v, w} P.op) : reduct (𝟙 P) m = m := by
  cases m
  rfl

theorem reduct_comp (h : P ⟶ Q) (k : Q ⟶ R) (m : Model.{u, v, w} R.op) :
    reduct (h ≫ k) m = reduct h (reduct k m) :=
  rfl

/-- An equation holds after relabelling exactly when it holds in the target model's reduct. -/
theorem Equation.satisfaction (h : P ⟶ Q) (e : Equation P) (m : Model.{u, v, w} Q.op) :
    (e.map h).Holds m ↔ e.Holds (reduct h m) :=
  Proofs.satisfaction h e m

/-- Translate sentences forwards and reduce models backwards along a typed opcode map. -/
@[expose] def corridor (h : P ⟶ Q) : room.{u, v, w} P ⟶ room.{u, v, w} Q :=
  ⟨Equation.map h, reductFunctor h, fun m e => e.satisfaction h m.as⟩

theorem corridor_id (P : Signature.{u, v} Data) :
    corridor.{u, v, w} (𝟙 P) = 𝟙 (room.{u, v, w} P) :=
  Room.hom_ext (funext Equation.map_id) (Discrete.functor_ext fun m => by cases m; rfl)

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    corridor.{u, v, w} (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext (funext (Equation.map_comp h k)) (Discrete.functor_ext fun _ => rfl)

/-- The source-native Sea of Nodes diamond institution over a fixed data alphabet. -/
@[expose] def inst (Data : Type u) :
    Inst.{max u (v + 1), max u v, max u v, max u v (w + 1), max u v (w + 1)} where
  Sign := Signature.{u, v} Data
  I := ⟨room.{u, v, w}, corridor.{u, v, w}, corridor_id, corridor_comp⟩

end Silmaril.SSA.SeaOfNodes.Diamond.Institution

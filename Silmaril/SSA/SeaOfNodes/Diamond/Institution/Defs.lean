module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.CategoryTheory.Discrete.Basic

/-! Equations of pure Sea of Nodes diamonds over a fixed alphabet of data sorts.
Signature morphisms relabel primitive operations at their exact typed profiles. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)

universe u v w

/-- The primitive signature over a fixed data alphabet and the distinguished predicate sort. -/
structure Signature (Data : Type u) where
  op : Diamond.Signature.{u, v} Data

variable {Data : Type u}

/-- Each opcode is mapped at its original ordered operand sorts and result sort. -/
structure Signature.Hom (P Q : Signature.{u, v} Data) where
  opcode : ∀ {ins out}, P.op ins out → Q.op ins out

instance : Category.{max u v} (Signature.{u, v} Data) where
  Hom := Signature.Hom
  id _ := ⟨fun op => op⟩
  comp h k := ⟨fun op => k.opcode (h.opcode op)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {P Q : Signature.{u, v} Data}
variable {args : List (Ty Data)} {sigs : List (List (Ty Data))}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}

/-- Relabel the existing typed data table and retain every producer number and wire. -/
def mapDataflow (h : P ⟶ Q) :
    {past sigs : List (List (Ty Data))} →
      Dataflow P.op args past sigs → Dataflow Q.op args past sigs
  | _, _, .nil => .nil
  | _, _, .cons op wires tail => .cons (Signature.Hom.opcode h op) wires (mapDataflow h tail)

/-- Relabel the producer opcodes and retain the predicate, Region order, and Phi wires. -/
def mapGraph (h : P ⟶ Q) (g : Graph P.op inputs sigs out) : Graph Q.op inputs sigs out :=
  ⟨mapDataflow h g.dataflow, g.predicate, g.phi⟩

/-- The reduct keeps the carriers and interprets a source opcode by its image. -/
def reduct (h : P ⟶ Q) (m : Model.{u, v, w} Q.op) : Model.{u, v, w} P.op where
  value := m.value
  run op := m.run (Signature.Hom.opcode h op)

/-- Equate two diamonds of the same ordered entry and result sorts.
The two sides may use different producer tables. -/
structure Equation (P : Signature.{u, v} Data) where
  inputs : List (ValueSort Data)
  out : ValueSort Data
  leftSigs : List (List (Ty Data))
  rightSigs : List (List (Ty Data))
  lhs : Graph P.op inputs leftSigs out
  rhs : Graph P.op inputs rightSigs out

/-- Translate both graphs while keeping the equation's boundary. -/
def Equation.map (h : P ⟶ Q) (e : Equation P) : Equation Q :=
  ⟨e.inputs, e.out, e.leftSigs, e.rightSigs, mapGraph h e.lhs, mapGraph h e.rhs⟩

/-- Satisfaction is agreement of the native source denotations at every typed input. -/
def Equation.Holds (e : Equation P) (m : Model.{u, v, w} P.op) : Prop :=
  ∀ entry : Tuple (Val m.value) (dataPorts e.inputs), e.lhs.denote m entry = e.rhs.denote m entry

def reductFunctor (h : P ⟶ Q) : Discrete (Model.{u, v, w} Q.op) ⥤ Discrete (Model.{u, v, w} P.op) :=
  Discrete.functor fun m => Discrete.mk (reduct h m)

/-- The room of native equations and discrete total models for a signature. -/
def room (P : Signature.{u, v} Data) :
    Room.{max u v, max u v (w + 1), max u v (w + 1)} where
  Sen := Equation P
  Mod := Cat.of (Discrete (Model.{u, v, w} P.op))
  Sat m e := e.Holds m.as

end Silmaril.SSA.SeaOfNodes.Diamond.Institution

module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Defs

/-! # Finite chains of pure arm-local diamonds -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}

/-- A boundary is a typed tuple. The preceding join supplies the next
stage's entire input, and different boundaries may have different types. -/
inductive Chain (Op : Signature.{u,v} Data) :
    List (ValueSort Data) → List (ValueSort Data) → Type (max u v) where
  | nil {inputs : List (ValueSort Data)} : Chain Op inputs inputs
  | cons {inputs middle results : List (ValueSort Data)} {sigs : List (List (Ty Data))}
      (head : Graph Op inputs sigs middle) (tail : Chain Op middle results) : Chain Op inputs results

def Chain.length : {inputs results : List (ValueSort Data)} → Chain Op inputs results → Nat
  | _, _, .nil => 0
  | _, _, .cons _ tail => tail.length + 1

variable (m : Model.{u,v,w} Op)

/-- Source execution composes the existing finite return relations. -/
def Chain.Returns : {inputs results : List (ValueSort Data)} → Chain Op inputs results →
    Tuple (Val m.value) (dataPorts inputs) → Tuple (Val m.value) (dataPorts results) → Prop
  | _, _, .nil, entry, result => entry = result
  | _, _, .cons head tail, entry, result =>
    ∃ joined, head.Returns m entry joined ∧ tail.Returns joined result

def Chain.denote : {inputs results : List (ValueSort Data)} → Chain Op inputs results →
    Tuple (Val m.value) (dataPorts inputs) → Tuple (Val m.value) (dataPorts results)
  | _, _, .nil, entry => entry
  | _, _, .cons head tail, entry => tail.denote (head.denote m entry)

end Silmaril.SSA.SeaOfNodes.Diamond.Arms

module

public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Defs

/-! # Execute the flat λSSA CFG emitted for a pure loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel

open Diamond (Model Val ValueSort dataPorts sortValue)
open Diamond.LambdaSSA (Atom Primitive encode)
open RVSDG (Tuple)
open Isotope (Value)
open Isotope.LambdaSSA (Region Tm)
open Isotope.LambdaSSA.Semantics (Env extend)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable (m : Model.{u, v, w} Op)

def decodeValue [DecidableEq Data] : (sort : ValueSort Data) →
    Value (Atom m) → Option (sortValue m.value sort)
  | .predicate, .inl .unit => some ⟨true⟩
  | .predicate, .inr .unit => some ⟨false⟩
  | .data sort, .atom ⟨tag, value⟩ =>
    if same : tag = sort then some (same ▸ value) else none
  | _, _ => none

def decodeArgs [DecidableEq Data] : (sorts : List (ValueSort Data)) →
    Value (Atom m) → Option (Tuple (Val m.value) (dataPorts sorts))
  | [], .unit => some .nil
  | sort :: rest, .pair head tail =>
    match decodeValue m sort head with
    | none => none
    | some value => (decodeArgs rest tail).map (.cons value)
  | _, _ => none

def execPrimitive [DecidableEq Data] : Primitive Op → Value (Atom m) → Option (Value (Atom m))
  | .apply (ins := ins) op, argument =>
    (decodeArgs m ins argument).map fun values => encode m (m.run op values)

variable [DecidableEq Data]

def evalTerm (env : Env (Atom m)) : Tm (Primitive Op) → Option (Value (Atom m))
  | .var i => some (env i)
  | .op op arg => (evalTerm env arg).bind (execPrimitive m op)
  | .unit => some .unit
  | .pair left right => return .pair (← evalTerm env left) (← evalTerm env right)
  | .inl arg => (evalTerm env arg).map .inl
  | .inr arg => (evalTerm env arg).map .inr
  | .let₁ arg body => do
      let value ← evalTerm env arg
      evalTerm (extend env value) body
  | .let₂ arg body => do
      let .pair left right ← evalTerm env arg | none
      evalTerm (extend (extend env left) right) body
  | .case discr left right => do
      match ← evalTerm env discr with
      | .inl value => evalTerm (extend env value) left
      | .inr value => evalTerm (extend env value) right
      | _ => none
  | .abort _ => none

abbrev Observation := Nat × Value (Atom m)

/-- Execute a flat entry or block until it branches. -/
def evalFlat (env : Env (Atom m)) : Region (Primitive Op) → Option (Observation m)
  | .br label arg => (evalTerm m env arg).map (label, ·)
  | .let₁ arg body => do
      let value ← evalTerm m env arg
      evalFlat (extend env value) body
  | .let₂ arg body => do
      let .pair left right ← evalTerm m env arg | none
      evalFlat (extend (extend env left) right) body
  | .case discr left right => do
      match ← evalTerm m env discr with
      | .inl value => evalFlat (extend env value) left
      | .inr value => evalFlat (extend env value) right
      | _ => none
  | .cfg .. => none

/-- Follow flat CFG blocks, charging one unit per local block activation.
The entry and transfers out of the CFG cost no fuel. -/
def follow (env : Env (Atom m)) {n : Nat} (blocks : Fin n → Region (Primitive Op)) :
    Nat → Observation m → Option (Observation m)
  | fuel, (label, payload) =>
    if inside : label < n then
      match fuel with
      | 0 => none
      | fuel + 1 => do
        let next ← evalFlat m (extend env payload) (blocks ⟨label, inside⟩)
        follow env blocks fuel next
    else some (label - n, payload)
termination_by structural fuel _ => fuel

/-- Run one existing flat λSSA CFG. On emitted code, `none` means exhaustion. -/
def run (env : Env (Atom m)) (fuel : Nat) : Region (Primitive Op) → Option (Observation m)
  | .cfg entry _ blocks => (evalFlat m env entry).bind (follow m env blocks fuel)
  | _ => none

end Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel

module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs
public import Silmaril.SSA.RVSDG.Institution.Defs

/-! A straight-line Sea of Nodes program reuses the typed producer table
introduced for the diamond. It returns one typed wire. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure

open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts sortValue)
open RVSDG (Origin Tuple extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}

/-- A single-result program. A result can refer to an input or any producer
in the table. Producer addresses are numbered from zero in dependency order. -/
structure Program (Op : Signature.{u, v} Data) (inputs : List (ValueSort Data))
    (out : ValueSort Data) where
  {sigs : List (List (Ty Data))}
  dataflow : Dataflow Op (dataPorts inputs) [] sigs
  result : Origin (dataPorts inputs) (extend [] sigs) (.value out)

/-- Evaluate the source table once in dependency order and read the returned wire. -/
def Program.eval (p : Program Op inputs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts inputs)) : sortValue m.value out :=
  Diamond.read m p.result entry (p.dataflow.eval m entry PUnit.unit)

/-- The target dialect lifts each source primitive at its ordered value profile. -/
inductive Opcode (Op : Signature.{u, v} Data) :
    RVSDG.Dialect.{u, max u v} (ValueSort Data) PEmpty.{u+1} where
  | primitive {ins : List (ValueSort Data)} {out : ValueSort Data} :
      Op ins out → Opcode Op (dataPorts ins) [.value out]

/-- Interpret each lifted opcode by the source model's primitive function. -/
abbrev toRVSDGModel (m : Model.{u, v, w} Op) : RVSDG.Model.{u, max u v, w} (Opcode Op) where
  value := sortValue m.value
  state := fun e => nomatch e
  run
    | .primitive op, input => .cons (m.run op input) .nil

variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}

/-- Emit one primitive binding per source producer, keeping the operand and result wires. -/
def lowerDataflow : {past sigs : List (List (Ty Data))} →
    Dataflow Op args past sigs → Origin args (extend past sigs) (.value out) →
    RVSDG.Term (Opcode Op) args past sigs [.value out]
  | _, _, .nil, result => .ret (.cons result .nil)
  | _, _, .cons op operands rest, result =>
    .bind ⟨_, .simple (.primitive op), operands, Fin.elim0⟩ (fun i => i.elim0)
      (lowerDataflow rest result)

/-- Collect the lowered bindings in the numbered RVSDG representation. -/
def Program.lower (p : Program Op inputs out) :
    RVSDG.Graph (Opcode Op) (dataPorts inputs) [] p.sigs [.value out] :=
  (lowerDataflow p.dataflow p.result).toGraph

/-- Two source programs at the same input and result types. Their producer
tables may have different numbers and types of intermediate results. -/
structure Equation (Op : Signature.{u, v} Data) (inputs : List (ValueSort Data))
    (out : ValueSort Data) where
  lhs : Program Op inputs out
  rhs : Program Op inputs out

/-- Satisfaction is equality of the native source results at every input. -/
def Equation.Holds (e : Equation Op inputs out) (m : Model.{u, v, w} Op) : Prop :=
  ∀ entry : Tuple (Val m.value) (dataPorts inputs), e.lhs.eval m entry = e.rhs.eval m entry

/-- Lower both sides to the existing RVSDG equation over the same typed boundary. -/
def Equation.toRVSDG (e : Equation Op inputs out) : RVSDG.Institution.Equation (Opcode Op) :=
  ⟨dataPorts inputs, [.value out], e.lhs.sigs, e.rhs.sigs, e.lhs.lower, e.rhs.lower⟩

end Silmaril.SSA.SeaOfNodes.Pure

module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs
public import Silmaril.SSA.RVSDG.Isomorphism.Defs

/-! Exact structural keys for the pure producer table, following Click,
PLDI ’95, §3.1. A key uses the opcode and the ordered addresses of its inputs. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN

open Diamond (Dataflow Signature Ty ValueSort dataPorts)
open RVSDG (Origin Port Wires extend)

universe u v

section Scope

variable {T : Type u} {args : List T} {t : T}

/-- Share the old addresses when one result tuple comes into scope. -/
def olderIndex (head : List T) : (scope : List (List T)) →
    Fin scope.length → Fin (scope ++ [head]).length
  | [], i => i.elim0
  | _ :: tail, i => Fin.cases ⟨0, Nat.zero_lt_succ _⟩ (fun j => (olderIndex head tail j).succ) i

def olderPort (head : List T) : (scope : List (List T)) → (i : Fin scope.length) →
    Port scope[i] t → Port (scope ++ [head])[olderIndex head scope i] t
  | [], i => i.elim0
  | first :: tail, i => Fin.cases
      (motive := fun j => Port (first :: tail)[j] t →
        Port ((first :: tail) ++ [head])[olderIndex head (first :: tail) j] t)
      id (fun j => olderPort head tail j) i

def weaken {past : List (List T)} (head : List T) : Origin args past t →
    Origin args (past ++ [head]) t
  | .arg port => .arg port
  | .output i port => .output (olderIndex head past i) (olderPort head past i port)

def newestIndex (head : List T) : (scope : List (List T)) → Fin (scope ++ [head]).length
  | [] => ⟨0, Nat.zero_lt_succ _⟩
  | _ :: tail => (newestIndex head tail).succ

def newestPort {head : List T} (port : Port head t) :
    (scope : List (List T)) → Port (scope ++ [head])[newestIndex head scope] t
  | [] => port
  | _ :: tail => newestPort port tail

def newest {past : List (List T)} {head : List T} (port : Port head t) :
    Origin args (past ++ [head]) t :=
  .output (newestIndex head past) (newestPort port past)

end Scope

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}

/-- Keep a wire's address while putting it in the final scope of a table. -/
def keepOrigin {t : Ty Data} :
    {past sigs : List (List (Ty Data))} → (flow : Dataflow Op args past sigs) →
      Origin args past t → Origin args (extend past sigs) t
  | _, _, .nil, wire => wire
  | scope, _, .cons (out := out) _ _ rest, wire =>
    keepOrigin (past := scope ++ [[.value out]]) rest (weaken [.value out] wire)

/-- A typed reference to an actual producer of the table. -/
inductive Producer : {past sigs : List (List (Ty Data))} →
    Dataflow Op args past sigs → ValueSort Data → Type (max u v) where
  | here {past sigs : List (List (Ty Data))} {ins : List (ValueSort Data)} {out : ValueSort Data}
      {op : Op ins out} {inputs : Wires args past (dataPorts ins)}
      {rest : Dataflow Op args (past ++ [[.value out]]) sigs} :
      Producer (.cons op inputs rest) out
  | later {past sigs : List (List (Ty Data))} {ins : List (ValueSort Data)} {out t : ValueSort Data}
      {op : Op ins out} {inputs : Wires args past (dataPorts ins)}
      {rest : Dataflow Op args (past ++ [[.value out]]) sigs} :
      Producer rest t → Producer (.cons op inputs rest) t

/-- The result's type is fixed by the reference. The key also keeps the input
types, opcode, and ordered typed input wires in the table's final scope. -/
structure Key (Op : Signature.{u,v} Data) (args : List (Ty Data))
    (scope : List (List (Ty Data))) (out : ValueSort Data) where
  ins : List (ValueSort Data)
  opcode : Op ins out
  operands : Wires args scope (dataPorts ins)

def Producer.origin :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → Producer flow out → Origin args (extend past sigs) (.value out)
  | scope, _, _, out, .here (rest := rest) =>
    keepOrigin (past := scope ++ [[.value out]]) rest (newest (past := scope) .head)
  | _, _, _, _, .later ref => ref.origin

def Producer.key :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → Producer flow out → Key Op args (extend past sigs) out
  | scope, _, _, out, .here (op := op) (inputs := inputs) (rest := rest) =>
    ⟨_, op, inputs.map (fun _ wire =>
      keepOrigin (past := scope ++ [[.value out]]) rest (weaken [.value out] wire))⟩
  | _, _, _, _, .later ref => ref.key

variable {out : ValueSort Data} {flow : Dataflow Op args past sigs}
variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- Compare exact opcodes at the same ordered type profile and compare
operand addresses in order, including repetitions. -/
def Key.matches (left right : Key Op args past out) : Bool :=
  if h : left.ins = right.ins then
    decide ((h ▸ left.opcode : Op right.ins out) = right.opcode) &&
      decide (left.operands.addresses = right.operands.addresses)
  else false

/-- Check one proposed earlier representative in the same table. -/
def checkRepresentative (candidate representative : Producer flow out) : Bool :=
  match candidate.origin.producer, representative.origin.producer with
  | some node, some earlier => decide (earlier < node) && candidate.key.matches representative.key
  | _, _ => false

/-- Redirect one selected result wire on acceptance, keeping the original
wire when the proposed representative is rejected. -/
def redirectResult (candidate representative : Producer flow out) :
    Origin args (extend past sigs) (.value out) :=
  if checkRepresentative candidate representative then representative.origin else candidate.origin

end Silmaril.SSA.SeaOfNodes.GVN

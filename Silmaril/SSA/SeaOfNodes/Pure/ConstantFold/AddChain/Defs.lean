module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Defs

/-! Combine the right literals of two adjacent additions on an add spine. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain

open Diamond (Dataflow Ty ValueSort dataPorts)
open GVN (newest weaken)
open GVN.Elimination (Rewrite Routing routeSuffix splitOrigin)
open SubZero (wordPort)
open RVSDG (Origin Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {ins : List (ValueSort Unit)} {out : ValueSort Unit}

abbrev WordWire (args : List (Ty Unit)) (past : List (List (Ty Unit))) :=
  Origin args past wordPort

/-- A wire plus a literal offset in the same typed prefix. -/
structure Offset (args : List (Ty Unit)) (past : List (List (Ty Unit))) where
  base : WordWire args past
  value : BitVec 64

structure Prefix (args : List (Ty Unit)) (past : List (List (Ty Unit))) where
  literals : Literals args past
  additions : WordWire args past → Option (Offset args past)

def Prefix.empty : Prefix args [] := ⟨fun _ => none, fun _ => none⟩

/-- An add with a literal right operand and a left operand without a literal
fact. Leave two-literal adds and the right identity to their existing rules. -/
def Prefix.rightLiteral? (known : Prefix args past) (lhs rhs : WordWire args past) :
    Option (Offset args past) :=
  match known.literals lhs, known.literals rhs with
  | none, some value =>
    let offset : BitVec 64 := value
    if offset = 0 then none else some ⟨lhs, offset⟩
  | _, _ => none

def Prefix.push (known : Prefix args past) (literal : Option (BitVec 64))
    (addition : Option (Offset args past)) : Prefix args (past ++ [[wordPort]]) where
  literals := Scan.Literals.push (out := SubZero.word) known.literals literal
  additions wire :=
    let prior := match splitOrigin [wordPort] wire with
      | .inl earlier => known.additions earlier
      | .inr .head => addition
      | .inr (.tail port) => nomatch port
    prior.map fun offset => ⟨weaken [wordPort] offset.base, offset.value⟩

def Prefix.record (known : Prefix args past) :
    (op : SubZero.Opcode ins out) → Wires args past (dataPorts ins) → Prefix args (past ++ [[.value out]])
  | .literal value, _ => known.push (some value) none
  | .add, .cons lhs (.cons rhs .nil) => known.push none (known.rightLiteral? lhs rhs)
  | .sub, _ | .mul, _ => known.push none none

def Prefix.combine? (known : Prefix args past) (lhs rhs : WordWire args past) :
    Option (Offset args past) := do
  let outer ← known.rightLiteral? lhs rhs
  let inner ← known.additions outer.base
  return ⟨inner.base, inner.value + outer.value⟩

/-- Insert the combined literal before the replacement add and route the
suffix through the new scope. Both original additions retain a result. -/
def insertCombined (offset : Offset args past) (rest : Dataflow SubZero.Opcode args (past ++ [[wordPort]]) sigs) :
    Rewrite SubZero.Opcode args past ([wordPort] :: sigs) :=
  let lift : Routing args past (past ++ [[wordPort]]) := fun wire => weaken [wordPort] wire
  let suffix := routeSuffix rest (lift.push [wordPort])
  ⟨_, .cons (.literal offset.value) .nil
    (.cons .add (.cons (lift offset.base) (.cons (newest .head) .nil)) suffix.1), suffix.2⟩

def atHead? (known : Prefix args past) :
    (op : SubZero.Opcode ins out) → Wires args past (dataPorts ins) →
    Dataflow SubZero.Opcode args (past ++ [[.value out]]) sigs → Option (Rewrite SubZero.Opcode args past ([.value out] :: sigs))
  | .add, .cons lhs (.cons rhs .nil), rest => (known.combine? lhs rhs).map (insertCombined · rest)
  | .literal _, _, _ | .sub, _, _ | .mul, _, _ => none

/-- Scan in dependency order and rewrite the first admitted outer addition. -/
def stepDataflow? : {past sigs : List (List (Ty Unit))} →
    Prefix args past → Dataflow SubZero.Opcode args past sigs → Option (Rewrite SubZero.Opcode args past sigs)
  | _, _, _, .nil => none
  | _, _, known, .cons op operands rest =>
    match atHead? known op operands rest with
    | some rewrite => some rewrite
    | none => (stepDataflow? (known.record op operands) rest).map fun rewrite =>
      ⟨_, .cons op operands rewrite.flow, rewrite.route⟩

variable {inputs : List (ValueSort Unit)}

/-- Try a single constant-chain rewrite. The result carries the typed map
from every original producer or argument wire to the rewritten table. -/
def step? (program : Program SubZero.Opcode inputs out) : Option (Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs) :=
  stepDataflow? Prefix.empty program.dataflow

/-- Read the original return through the rewrite's typed map. -/
def rewrittenProgram (program : Program SubZero.Opcode inputs out)
    (rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs) : Program SubZero.Opcode inputs out :=
  { dataflow := rewrite.flow, result := rewrite.route program.result }

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain

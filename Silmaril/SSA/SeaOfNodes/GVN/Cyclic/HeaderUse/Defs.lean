module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Defs

/-!
# One checked header operand substitution

The target is a producer of the actual header table and one of its typed
operand ports. The caller supplies a proposed class member and a wire in the
target's actual prefix. The checker ties both the old operand and the supplied
prefix wire to their represented sources before editing the operand.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse

open Diamond (Dataflow Signature Ty ValueSort dataPorts)
open RVSDG (Origin Port Wires)
open Elimination (inFinal operandScope)
open Activation (View sourceWire)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {out sort : ValueSort Data} {t : Ty Data} {flow : Dataflow Op args past sigs}

/-- The old wire at this precise argument occurrence, in the consumer's prefix. -/
def operandAt :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → (consumer : Producer flow out) →
        Port (dataPorts consumer.key.ins) t → Origin args (operandScope consumer) t
  | _, _, _, _, .here (inputs := operands), use => operands.get use
  | _, _, _, _, .later consumer, use => operandAt consumer use

/-- Replace one tuple position. Repeated reads of the same source elsewhere
in the tuple are separate occurrences. -/
def setOperand {ports : List (Ty Data)} :
    Port ports t → Origin args past t → Wires args past ports → Wires args past ports
  | .head, replacement, .cons _ tail => .cons replacement tail
  | .tail use, replacement, .cons head tail => .cons head (setOperand use replacement tail)

/-- Edit one binding's selected operand and retain the table's signatures. -/
def replaceAt :
    {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
      {out : ValueSort Data} → (consumer : Producer flow out) →
        Port (dataPorts consumer.key.ins) t → Origin args (operandScope consumer) t →
          Dataflow Op args past sigs
  | _, _, _, _, .here (op := opcode) (inputs := operands) (rest := rest), use, replacement =>
    .cons opcode (setOperand use replacement operands) rest
  | _, _, _, _, .later (op := opcode) (inputs := operands) consumer, use, replacement =>
    .cons opcode operands (replaceAt consumer use replacement)

variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {n : Nat} {sorts : Fin n → ValueSort Data}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable {g : Cyclic.Graph Op inputs sorts} {consumerOut : ValueSort Data}
variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- Match the actual operand and the supplied prefix wire to their typed
class sources. An equivalent source later in the table cannot pass the
address check through a different, earlier wire. -/
def check (view : View g loop) (p : Partition n) (consumer : Producer loop.header consumerOut)
    (use : Port (dataPorts consumer.key.ins) (.value sort))
    (original representative : Source inputs sorts sort)
    (prefixWire : Origin (Loop.headerPorts inputs carried) (operandScope consumer) (.value sort)) :
    Bool :=
  checkStable g p &&
    decide (original.address.relabel p = representative.address.relabel p) &&
    decide ((inFinal consumer (operandAt consumer use)).address = (sourceWire view.site original).address) &&
    decide ((inFinal consumer prefixWire).address = (sourceWire view.site representative).address)

/-- The optional rewrite edits only the checked occurrence of the header. -/
def redirect? (view : View g loop) (p : Partition n) (consumer : Producer loop.header consumerOut)
    (use : Port (dataPorts consumer.key.ins) (.value sort))
    (original representative : Source inputs sorts sort)
    (prefixWire : Origin (Loop.headerPorts inputs carried) (operandScope consumer) (.value sort)) :
    Option (Loop.Graph Op inputs carried entrySigs headerSigs out) :=
  if check view p consumer use original representative prefixWire then
    some { loop with header := replaceAt consumer use prefixWire }
  else none

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse

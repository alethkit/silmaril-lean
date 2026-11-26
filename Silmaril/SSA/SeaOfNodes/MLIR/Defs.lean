module

public import Silmaril.SSA.MLIR.Arith.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Defs

/-! # Sea of Nodes pure producers in scalar MLIR

Bind each producer in the existing dependency order. An input or producer
address is resolved to the corresponding in-scope scalar SSA variable.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.MLIR

open RVSDG (Port Tuple Origin Wires Locals extend)
open Diamond (Dataflow Val dataPorts)
open Silmaril.MLIR.Arith (BinOp Block Env Rhs Var Width)

abbrev Word (w : Width) := BitVec w.val

/-- The flag-free scalar operation profiles shared by the pure source and Arith. -/
inductive Op : Diamond.Signature.{0, 0} Width where
  | constant {w : Width} (value : Word w) : Op [] (.data w)
  | binary {w : Width} (op : BinOp) : Op [.data w, .data w] (.data w)

/-- The pure source model on fixed-width words. -/
def model : Diamond.Model Op where
  value := Word
  run
    | .constant value, .nil => value
    | .binary .addi, .cons x (.cons y .nil) => BitVec.add x y
    | .binary .muli, .cons x (.cons y .nil) => BitVec.mul x y

abbrev inputPorts (Γ : List Width) : List (Diamond.Ty Width) :=
  dataPorts (Γ.map Diamond.ValueSort.data)

/-- Read the source input ports in the same order as the block arguments. -/
def sourceInputs : {Γ : List Width} → Env Γ → Tuple (Val Word) (inputPorts Γ)
  | _, .nil => .nil
  | _, .cons value tail => .cons value (sourceInputs tail)

namespace Lowering

/-- Only word ports have scalar SSA names. The other cases have no names and
cannot be used by any operation in this bridge. -/
def Names (Γ : List Width) : Diamond.Ty Width → Type
  | .value (.data w) => Var Γ w
  | _ => PUnit

variable {Γ : List Width} {args : List (Diamond.Ty Width)} {past sigs : List (List (Diamond.Ty Width))}

def weaken (v : Width) (t : Diamond.Ty Width) : Names Γ t → Names (v :: Γ) t :=
  match t with
  | .value (.data _) => Var.there
  | .value .predicate | .state _ | .control _ => id

def inputNames : (Γ : List Width) → Tuple (Names Γ) (inputPorts Γ)
  | [] => .nil
  | v :: Γ => .cons Var.here ((inputNames Γ).map (weaken v))

structure Scope (args : List (Diamond.Ty Width)) (past : List (List (Diamond.Ty Width))) (Γ : List Width) where
  inputs : Tuple (Names Γ) args
  locals : Locals (Names Γ) past

/-- Keep the source producer numbering and extend its name table by one result. -/
def pushLocal (v : Width) : {past : List (List (Diamond.Ty Width))} → Locals (Names Γ) past →
    Locals (Names (v :: Γ)) (past ++ [[.value (.data v)]])
  | [], _ => (.cons Var.here .nil, PUnit.unit)
  | _ :: _, locals => (locals.1.map (weaken v), pushLocal v locals.2)

def Scope.push (scope : Scope args past Γ) (v : Width) :
    Scope args (past ++ [[.value (.data v)]]) (v :: Γ) :=
  ⟨scope.inputs.map (weaken v), pushLocal v scope.locals⟩

def Scope.resolve (scope : Scope args past Γ) {w : Width} :
    Origin args past (.value (.data w)) → Var Γ w
  | .arg port => scope.inputs.get port
  | .output i port => (scope.locals.get i).get port

def emit (scope : Scope args past Γ) {ins : List (Diamond.ValueSort Width)}
    {w : Width} (op : Op ins (.data w))
    (wires : Wires args past (dataPorts ins)) : Rhs Γ w :=
  match op, wires with
  | .constant value, .nil => .constant value
  | .binary op, .cons x (.cons y .nil) => .binary op (scope.resolve x) (scope.resolve y)

def lowerFrom {w : Width} : {past sigs : List (List (Diamond.Ty Width))} → {Γ : List Width} →
    (flow : Dataflow Op args past sigs) → Scope args past Γ →
    Origin args (extend past sigs) (.value (.data w)) → Block Γ w
  | _, _, _, .nil, scope, result => .yield (scope.resolve result)
  | _, _, _, .cons (.constant (w := v) value) wires rest, scope, result =>
      .letOp (emit scope (.constant value) wires) (lowerFrom rest (scope.push v) result)
  | _, _, _, .cons (.binary (w := v) op) wires rest, scope, result =>
      .letOp (emit scope (.binary op) wires) (lowerFrom rest (scope.push v) result)

end Lowering

/-- Lower the pure producers of a Sea of Nodes data table to a straight-line
Arith block. The caller selects one word-valued input or producer as the result. -/
def lower {Γ : List Width} {sigs : List (List (Diamond.Ty Width))} {w : Width}
    (flow : Dataflow Op (inputPorts Γ) [] sigs)
    (result : Origin (inputPorts Γ) (extend [] sigs) (.value (.data w))) : Block Γ w :=
  Lowering.lowerFrom flow ⟨Lowering.inputNames Γ, PUnit.unit⟩ result

end Silmaril.SSA.SeaOfNodes.MLIR

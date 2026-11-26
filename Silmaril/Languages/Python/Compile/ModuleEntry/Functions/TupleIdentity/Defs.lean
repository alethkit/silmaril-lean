module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs
public import Silmaril.Languages.Python.Core.Closure.Defs

/-! # A checked identity operand for exact module tuples -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleIdentity

open Core.Closure (Heap Value)
open Source (Scope)

inductive Operand where
  | global (name : String)
  | empty

structure Test where
  left : Operand
  operator : Core.Module.IdentityOperator
  right : Operand

inductive Translates (scope : Scope) : Source.Expr → Operand → Prop where
  | global (name : String) (reference : GlobalReference scope name) :
      Translates scope (.name name) (.global name)
  | empty : Translates scope (.tuple []) .empty

def checkOperand (scope : Scope) : (source : Source.Expr) → Option {operand // Translates scope source operand}
  | .name name => (globalReference? scope name).map fun reference => ⟨.global name, .global name reference⟩
  | .tuple [] => some ⟨.empty, .empty⟩
  | _ => none

inductive Argument (scope : Scope) : List (Source.ArgumentKind × Source.Expr) → Test → Prop where
  | test {left right comparison operator lhs rhs}
      (identity : identityOperator? comparison = some operator)
      (first : Translates scope left lhs) (second : Translates scope right rhs) :
      Argument scope [(.positional, .comparison left [(comparison, right)])] ⟨lhs, operator, rhs⟩

def checkArgument (scope : Scope) : (arguments : List (Source.ArgumentKind × Source.Expr)) →
    Option {test // Argument scope arguments test}
  | [(.positional, .comparison first [(comparison, second)])] => do
    let lhs ← checkOperand scope first
    let rhs ← checkOperand scope second
    match checked : identityOperator? comparison with
    | some operator => some ⟨⟨lhs.val, operator, rhs.val⟩, .test checked lhs.property rhs.property⟩
    | none => none
  | _ => none

inductive Identity where
  | empty
  | allocated (address : Nat)
  deriving DecidableEq

/-- The reference must resolve against the heap paired with the live namespace.
The payload check validates a descriptor. Identity compares only its address. -/
def identify (heap : Heap) : Value → Option Identity
  | .tuple [] | .tupleObject ⟨none, []⟩ => some .empty
  | .tupleObject ⟨some address, first :: rest⟩ =>
    match heap.lookup ⟨address⟩ with
    | some (some (.tuple stored)) => if stored = first :: rest then some (.allocated address) else none
    | _ => none
  | _ => none

/-- Repeated reads of the same binding have one object even when the tuple
only carries its contents. Different bindings need persistent identity. -/
def sameOpaqueRead (test : Test) (left right : Value) : Bool :=
  match test.left, test.right, left, right with
  | .global first, .global second, .tuple (_ :: _), .tuple (_ :: _) => first == second
  | _, _, _, _ => false

def Test.compare (test : Test) (heap : Heap) (left right : Value) : Option Bool :=
  let same := match identify heap left, identify heap right with
    | some first, some second => some (decide (first = second))
    | _, _ => if sameOpaqueRead test left right then some true else none
  same.map fun equal => match test.operator with
    | .is_ => equal
    | .isNot => !equal

def Operand.read {ε : Type} (lookup : String → Except ε (Option Value)) :
    Operand → Except ε (Option Value)
  | .global name => lookup name
  | .empty => .ok (some (.tuple []))

/-- Lookup errors take precedence over unsupported identity. Both successful
operands are needed before the comparison can classify their provenance. -/
def Test.evaluate {ε : Type} (test : Test) (heap : Heap)
    (lookup : String → Except ε (Option Value)) (unsupported : ε) : Except ε Bool := do
  let left ← test.left.read lookup
  let right ← test.right.read lookup
  match left.bind (fun first => right.bind (test.compare heap first)) with
  | some result => .ok result
  | none => .error unsupported

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleIdentity

module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Defs

/-! # Infer the cut at a nested-feedback leaf followed by a structured suffix -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse

open Sequential
open Sequential.Flat.Serial (Joined)
open NestedFeedback.Reverse (Key PrimitiveReader readTheta readOuterWith)
open Flat.Numbered.Recognize (OpcodeKey opcodeKey opcodeCode)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

structure CutLayout (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] where
  input : τ
  join : τ
  left : τ
  right : τ
  nested : Key τ Φ × Key τ Φ × Key τ Φ
  suffix : List (Ports (OrderedRuntime.Structured.Ty τ))
  layout : StructuredCFG.Reverse.Layout τ Φ

def readOpcode : PrimitiveReader (Wires.Op (τ := τ) Φ) (OpcodeKey τ Φ)
  | _, _, .base (.simple op) => some (opcodeKey op)
  | _, _, _ => none

def readNested : PrimitiveReader (Wires.Op (τ := τ) Φ) (Key τ Φ) :=
  fun kind => (readOpcode kind).bind fun
    | .nested op => some op
    | _ => none

def enterTypes : PrimitiveReader (Wires.Op (τ := τ) Φ) (τ × τ) :=
  fun kind => (readOpcode kind).bind fun
    | .enterNested a m => some (a, m)
    | _ => none

def exitTypes : PrimitiveReader (Wires.Op (τ := τ) Φ) (τ × τ) :=
  fun kind => (readOpcode kind).bind fun
    | .exitNested a m => some (a, m)
    | _ => none

def linkTypes : PrimitiveReader (Wires.Op (τ := τ) Φ) ((τ × τ) × τ × τ) :=
  fun kind => (readOpcode kind).bind fun
    | .link a m i j => some ((a, m), i, j)
    | _ => none

def suffixLayout {args outs : Ports (OrderedRuntime.Structured.Ty τ)}
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
    (term : NestedTheta.Term (Wires.Op Φ) args past sigs outs) :
    Option (List (Ports (OrderedRuntime.Structured.Ty τ)) × StructuredCFG.Reverse.Layout τ Φ) :=
  (StructuredCFG.Reverse.scan term).map fun labels => (sigs, labels)

variable [DecidableEq τ]

/-- Inspect the two carrier conversions and the actual link. Read the
suffix where it sits in the graph. Wire origins are checked at certification. -/
def readTerm {args outs : Ports (OrderedRuntime.Structured.Ty τ)} :
    {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term (Wires.Op Φ) args [] sigs outs → Option (CutLayout τ Φ)
  | [], _ | [_], _ | [_,_], _ | [_,_,_], _ => none
  | _ :: _ :: _ :: _ :: _, term =>
    match term with
    | .bind enter _ (.bind loop body (.bind exit _ (.bind cut _ rest))) => do
      let (a, m) ← enterTypes enter.kind
      let exitBoundary ← exitTypes exit.kind
      let (cutBoundary, i, j) ← linkTypes cut.kind
      if exitBoundary = (a, m) ∧ cutBoundary = (a, m) then
        let labels ← readTheta loop.kind body (readOuterWith readNested)
        let (sigs, tail) ← suffixLayout rest
        return ⟨a, m, i, j, labels, sigs, tail⟩
      else none

def read (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (CutLayout τ Φ) :=
  readTerm g.toTerm

/-- Reconstruct typed local views using the standalone nested decoder and
the structured suffix decoder. Both share the same inferred join type. -/
def decode (c : CutLayout τ Φ) : Option (Syntax Φ A X Z L E D sigs) := do
  if c.input = A then
    if hx : c.join = X then
      if hz : c.join = Z then
        let ⟨_, _, nested⟩ ← NestedFeedback.Reverse.decode (A := A) (D := c.join) c.nested
        let tail ← StructuredCFG.Reverse.decodeLayout
          (A := c.join) (X := c.left) (Z := c.right) (L := L) (E := E) (D := D) (sigs := c.suffix) c.layout
        if hs : Joined c.join c.left c.right (Leaf.Sigs A c.join) c.suffix = sigs then
          return hs ▸ hx ▸ hz ▸ Syntax.link (.nested nested) (.structured tail.toSyntax)
        else none
      else none
    else none
  else none

def candidate (g : Flat.Serial.Graph Φ A X Z L E D sigs) :
    Option (Syntax Φ A X Z L E D sigs) :=
  (read g).bind decode

variable [DecidableEq Φ]

/-- Compare the complete typed re-emission with the input, including both
cross-cut operands, the token returned by the adapter, and nested scopes. -/
def certify (g : Flat.Serial.Graph Φ A X Z L E D sigs) (view : Syntax Φ A X Z L E D sigs) :
    Option (Decomposition g) :=
  letI := NestedTheta.Equality.decideGraph (opcodeCode (τ := τ) (Φ := Φ)) view.graph g
  if same : view.graph = g then some ⟨view, same⟩ else none

def recover (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (Fibre g) :=
  (candidate g >>= certify g).map Decomposition.raise

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse

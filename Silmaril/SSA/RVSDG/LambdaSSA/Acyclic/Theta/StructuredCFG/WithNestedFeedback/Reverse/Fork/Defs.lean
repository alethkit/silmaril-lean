module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Defs

/-! # Recover a mixed fork with a nested-feedback right arm -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Fork

open Sequential
open NestedFeedback.Reverse (RegionReader)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

abbrev Scope (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] :=
  List (Ports (OrderedRuntime.Structured.Ty τ)) × StructuredCFG.Reverse.Layout τ Φ

structure Layout (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] where
  gate : Wires.Reverse.Vertex (τ := τ) (Φ := Φ)
  left : Scope τ Φ
  right : CutLayout τ Φ
  tail : Scope τ Φ

variable [DecidableEq τ]

/-- The arms start in their own numbered regions. Only the structured
left arm has the leading connector that extracts the classifier payload. -/
def readArms : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Wires.Op Φ) ins outs) →
    {sigs : Fin kind.arity → List (Ports (OrderedRuntime.Structured.Ty τ))} →
    ((j : Fin kind.arity) → NestedTheta.Term (Wires.Op Φ) kind.entry [] (sigs j) kind.exit) →
    Option (Scope τ Φ × CutLayout τ Φ)
  | _, _, .base (.gamma 0), _, arms => do
    return (← suffixLayout (arms (0 : Fin 2)), ← readTerm (arms (1 : Fin 2)))
  | _, _, _, _, _ => none

def readFork : RegionReader (Wires.Op (τ := τ) Φ) (Layout τ Φ)
  | _, _, [], _ | _, _, [_], _ => none
  | _, _, _ :: _ :: _, term =>
    match term with
    | .bind gate _ (.bind fork arms tail) => do
      let gate ← Wires.Reverse.readKind gate.kind (fun _ => none)
      let (left, right) ← readArms fork.kind arms
      let tail ← suffixLayout tail
      return ⟨gate, left, right, tail⟩

def read (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (Layout τ Φ) :=
  readFork g.toTerm

/-- Decode a root fork whose right arm ends at the inferred join connector.
Its ordinary left arm and shared tail use the existing structured decoder. -/
def decode : Layout τ Φ → Option (Syntax Φ A X Z L E D sigs)
  | ⟨.classifier (A := a) (X := x) (Y := y) gate, (leftSigs, .atom (.cut first payload left right) :: rest), nested, tail⟩ =>
    let m := nested.join
    let b := nested.input
    let i := nested.left
    let j := nested.right
    if typed : a = A ∧ Silmaril.coprod x y = ChoiceCarrier m b then
      if (first,payload,left,right) = (b,m,m,m) ∧ nested.suffix = [] then do
        let (boundary, labels) ← StructuredCFG.Reverse.splitArm rest
        if boundary.left = i ∧ boundary.right = j then
          let p ← StructuredCFG.Reverse.decodeLayout
            (A := m) (X := m) (Z := m) (L := boundary.carry) (E := m) (D := m)
            (sigs := leftSigs.tail.dropLast) labels
          let ⟨_, _, q⟩ ← NestedFeedback.Reverse.decode (A := b) (D := m) nested.nested
          let k ← StructuredCFG.Reverse.decodeLayout (A := m) (X := i) (Z := j) (L := L) (E := E) (D := D)
            (sigs := tail.1) tail.2
          if hs : Selection m b i j ++ tail.1 = sigs then
            return hs ▸ Syntax.branch (typed.1 ▸ typed.2 ▸ gate)
              (.structured p.toSyntax) (.nested q) (.structured k.toSyntax)
          else none
        else none
      else none
    else none
  | _ => none

def candidate (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (Syntax Φ A X Z L E D sigs) :=
  (read g).bind decode

variable [DecidableEq Φ]

/-- Use the mixed serial recognizer's exact graph comparison on the
reconstructed fork, including all arm-local and shared continuation wires. -/
def recover (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (Fibre g) :=
  (candidate g >>= certify g).map Decomposition.raise

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Fork

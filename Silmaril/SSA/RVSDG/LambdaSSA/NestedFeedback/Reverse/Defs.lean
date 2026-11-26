module

public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Opcode.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Decision.Defs

/-! # Recover the two-header flat CFG from the numbered nested graph -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse

open Isotope.LambdaSSA (Region)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A D : τ}

abbrev View (Φ : Type u) [HasTy Φ τ] (A D : τ) := Σ B K : τ, Loop Φ A B K D

def readPrimitive {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} :
    NestedTheta.Kind (Op Φ) ins outs → Option (Key τ Φ)
  | .base (.simple op) => some (opcodeKey op)
  | _ => none

abbrev RegionReader (P : Dialect.{u,u} τ PUnit.{u+1}) (X : Type u) :=
  {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term P ins [] sigs outs → Option X

abbrev PrimitiveReader (P : Dialect.{u,u} τ PUnit.{u+1}) (X : Type u) :=
  {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} → NestedTheta.Kind P ins outs → Option X

abbrev Reader (Φ : Type u) [HasTy Φ τ] (X : Type u) := RegionReader (Op (τ := τ) Φ) X

variable {P : Dialect.{u,u} τ PUnit.{u+1}}

def readTheta {X : Type u} {ins outs : Ports (OrderedRuntime.Structured.Ty τ)}
    (kind : NestedTheta.Kind P ins outs)
    {sigs : Fin kind.arity → List (Ports (OrderedRuntime.Structured.Ty τ))}
    (children : (j : Fin kind.arity) → NestedTheta.Term P kind.entry [] (sigs j) kind.exit)
    (readChild : RegionReader P X) : Option X :=
  match kind with
  | .theta _ => readChild (children (0 : Fin 1))
  | .base _ => none

def readInnerWith {X : Type u} (primitive : PrimitiveReader P X) : RegionReader P X
  | _, _, [_], term =>
    match term with
    | .bind inner _ (.ret _) => primitive inner.kind
  | _, _, _, _ => none

/-- Read the nested feedback layout in any port-preserving opcode embedding. -/
def readOuterWith {X : Type u} (primitive : PrimitiveReader P X) : RegionReader P (X × X × X)
  | _, _, [_,_,_], term =>
    match term with
    | .bind enter _ (.bind inner children (.bind finish _ (.ret _))) => do
      return (← primitive enter.kind, ← readTheta inner.kind children (readInnerWith primitive),
        ← primitive finish.kind)
  | _, _, _, _ => none

def readInner : Reader (τ := τ) Φ (Key τ Φ) := readInnerWith readPrimitive

def readOuter : Reader (τ := τ) Φ (Key τ Φ × Key τ Φ × Key τ Φ) := readOuterWith readPrimitive

/-- Inspect the outer θ and its inner θ, collecting the three opcode roles.
The shape parser leaves wire comparison to certification. -/
def read (g : Graph Φ A D) : Option (Key τ Φ × Key τ Φ × Key τ Φ) :=
  match g.toTerm with
  | .bind outer children (.ret _) => readTheta outer.kind children readOuter

variable [DecidableEq τ]

def instructionAt (op : Φ) (src dst : τ) : Option (TwoBlock.Instruction Φ src dst) :=
  if hi : instrSrc op = src then
    if ho : instrTrg op = dst then some ⟨op, hi, ho⟩ else none
  else none

def decode : Key τ Φ × Key τ Φ × Key τ Φ → Option (View Φ A D)
  | (.enter a b k d enter, .inner b' k' inner, .finish a'' b'' k'' d'' finish) =>
    if a = A ∧ d = D ∧ b' = b ∧ k' = k ∧ a'' = A ∧ b'' = b ∧ k'' = k ∧ d'' = D then do
      return ⟨b, k, ⟨← instructionAt enter A b, ← instructionAt inner b (Carrier b k),
        ← instructionAt finish k (Carrier A D)⟩⟩
    else none
  | _ => none

/-- Infer the two inner boundary types and reconstitute typed instruction
applications from the graph's opcode annotations and the signature. -/
def candidate (g : Graph Φ A D) : Option (View Φ A D) := (read g).bind decode

structure Match (g : Graph Φ A D) where
  view : View Φ A D
  wiring : graph view.2.2 = g

variable [DecidableEq Φ]

deriving instance DecidableEq for PortType

/-- Compare re-emission with the whole graph, recursively checking every
operand, return, nested vertex and token origin. -/
def certify (g : Graph Φ A D) (view : View Φ A D) : Option (Match g) :=
  letI := NestedTheta.Equality.decideGraph (opcodeCode (τ := τ) (Φ := Φ)) (graph view.2.2) g
  if same : graph view.2.2 = g then some ⟨view, same⟩ else none

def recognize (g : Graph Φ A D) : Option (Match g) := (candidate g).bind (certify g)

/-- A recovered region indexed by the graph it lowers to. -/
structure Fibre (g : Graph Φ A D) where
  innerInput : τ
  innerResult : τ
  source : Region Φ
  witness : Related A innerInput innerResult D source g

def Match.raise {g : Graph Φ A D} (m : Match g) : Fibre g :=
  let s := m.view.2.2
  ⟨m.view.1, m.view.2.1, region s,
    Eq.mp (congrArg (Related A m.view.1 m.view.2.1 D (region s)) m.wiring) (.generated s)⟩

/-- Recover a typed flat source and its exact relation witness from the
numbered graph. Neither the source nor its internal types are inputs. -/
def recover (g : Graph Φ A D) : Option (Fibre g) := (recognize g).map Match.raise

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse

module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Check.Defs

/-! # Recover the diamond from its numbered vertex table -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse

open Isotope.LambdaSSA (Region)
open Sequential.Flat.Serial.Recognize (Mark scan mark)
open Sequential.Flat.Numbered.Recognize (loop opcodeCode)
open Sequential.Wires.Reverse (Vertex readKind readBody)
open TwoBlock.TwoExit (Carrier)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A M Y E D : τ}

structure Layout (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] where
  selector : Vertex (τ := τ) (Φ := Φ)
  left : List (Mark τ Φ)
  right : List (Mark τ Φ)
  tail : Mark τ Φ

def readArms : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Sequential.Wires.Op Φ) ins outs) →
    {sigs : Fin kind.arity → List (Ports (OrderedRuntime.Structured.Ty τ))} →
    ((j : Fin kind.arity) → NestedTheta.Term (Sequential.Wires.Op Φ) kind.entry [] (sigs j) kind.exit) →
    Option (List (Mark τ Φ) × List (Mark τ Φ))
  | _, _, .base (.gamma 0), _, children => do
    return (← scan (children (0 : Fin 2)), ← scan (children (1 : Fin 2)))
  | _, _, _, _, _ => none

/-- Read the classifier, the two local γ regions and the shared θ.
The serial scanner supplies each child's label tree and size bound. -/
def read (g : Graph Φ A M Y E D) : Option (Layout τ Φ) :=
  match g.toTerm with
  | .bind gate children (.bind fork arms (.bind tail body (.ret _))) => do
    let selector ← readKind gate.kind (fun j => readBody (children j))
    let (left, right) ← readArms fork.kind arms
    let next ← mark tail.kind body
    return ⟨selector, left, right, next⟩

variable [DecidableEq τ]

/-- Decode with the graph's typed boundaries. Connector occurrences locate
the loops. Their annotations and all wire addresses are checked by certification. -/
def decode : Layout τ Φ → Option (Diamond Φ A M Y E D)
  | ⟨.classifier (A := a) (X := x) (Y := y) op,
      [.cut _ _ _ _, .loop lf left, .cut _ _ _ _],
      [.loop rf right, .cut _ _ _ _], .loop tf tail⟩ =>
    if ha : a = A then
      if ho : Silmaril.coprod x y = Carrier Y M M then do
        let ⟨lb, lj, left⟩ ← loop lf M M M left
        let ⟨rb, rj, right⟩ ← loop rf Y M M right
        let ⟨tb, tj, tail⟩ ← loop tf M E D tail
        return ⟨ha ▸ ho ▸ op, lb, lj, rb, rj, tb, tj, left, right, tail⟩
      else none
    else none
  | _ => none

def candidate (g : Graph Φ A M Y E D) : Option (Diamond Φ A M Y E D) :=
  (read g).bind decode

/-- A parsed diamond whose reconstructed graph is exactly the input. -/
structure Match (g : Graph Φ A M Y E D) where
  view : Diamond Φ A M Y E D
  wiring : graph view = g

variable [DecidableEq Φ]

/-- Compare the whole typed graph recursively, including selector, payload
and token origins at the γ, θ and return boundaries. -/
def certify (g : Graph Φ A M Y E D) (view : Diamond Φ A M Y E D) : Option (Match g) :=
  letI := NestedTheta.Equality.decideGraph (opcodeCode (τ := τ) (Φ := Φ)) (graph view) g
  if same : graph view = g then some ⟨view, same⟩ else none

def recognize (g : Graph Φ A M Y E D) : Option (Match g) :=
  (candidate g).bind (certify g)

abbrev Fibre (g : Graph Φ A M Y E D) := Σ r : Region Φ, Related A M Y E D r g

omit [DecidableEq τ] [DecidableEq Φ] in
def Match.raise {g : Graph Φ A M Y E D} (d : Match g) : Fibre g :=
  let r := (source d.view).region
  ⟨r, Eq.mp (congrArg (Related A M Y E D r) d.wiring) (.diamond d.view)⟩

/-- Compute an actual flat CFG and relation witness from the numbered graph. -/
def recover (g : Graph Φ A M Y E D) : Option (Fibre g) :=
  (recognize g).map Match.raise

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse

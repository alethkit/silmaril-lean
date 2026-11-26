module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Defs

/-! # Reverse recovery for the numbered two-loop family -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse

open Isotope.LambdaSSA (Region)
open NestedTheta.ExplicitRuntime (EntryChecked)
open OrderedTheta (carriedData)
open OrderedRuntime.Structured (Threaded)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K M C J E D : τ}

abbrev Vertex := ExplicitRuntime.Reverse.Vertex τ Φ

def readKind :
    {ins out : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Op Φ) ins out) →
    (Fin kind.arity → Option (List (Vertex (τ := τ) (Φ := Φ)))) → Option (Vertex (τ := τ) (Φ := Φ))
  | _, _, .base (.simple (.ordered _ _ (.pure p))), _ =>
    some (ExplicitRuntime.Reverse.primitive (.pure p))
  | _, _, .base (.simple (.ordered _ _ (.effect (.loop op)))), _ =>
    some (ExplicitRuntime.Reverse.primitive (.effect op))
  | _, _, .base (.simple (.ordered _ _ (.effect _))), _ => none
  | _, _, .base (.gamma _), children => .gamma <$> (List.ofFn children).mapM id
  | _, _, .theta _, children => .theta <$> children (0 : Fin 1)

/-- Read a local loop region using the single-loop vocabulary. A link is
allowed at the outer boundary only. -/
def readBody :
    {args outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term (Op Φ) args past sigs outs → Option (List (Vertex (τ := τ) (Φ := Φ)))
  | _, _, _, _, .ret _ => some []
  | _, _, _, _, .bind node children rest => do
    let head ← readKind node.kind (fun j => readBody (children j))
    let tail ← readBody rest
    pure (head :: tail)

abbrev ClosedTerm (Φ : Type u) [HasTy Φ τ] (A M E D : τ) :=
  NestedTheta.Term (Op Φ) (Threaded (FirstPorts A M)) [] (Signatures A M E D)
    (Threaded (SecondPorts M E D))

def effectIsLink : {ins out : Ports (OrderedRuntime.Structured.Ty τ)} → Effect Φ ins out → Bool
  | _, _, .link => true
  | _, _, _ => false

def isLink : {ins out : Ports (OrderedRuntime.Structured.Ty τ)} →
    NestedTheta.Kind (Op Φ) ins out → Bool
  | _, _, .base (.simple (.ordered _ _ (.effect e))) => effectIsLink e
  | _, _, _ => false

def readTheta : {ins out : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Op Φ) ins out) →
    (Fin kind.arity → Option (List (Vertex (τ := τ) (Φ := Φ)))) → Option (List (Vertex (τ := τ) (Φ := Φ)))
  | _, _, .theta _, children => children (0 : Fin 1)
  | _, _, _, _ => none

/-- Read the actual outer wrapper as two θ vertices around a single typed
link. Wire addresses are certified separately. -/
def read (t : ClosedTerm Φ A M E D) :
    Option (List (Vertex (τ := τ) (Φ := Φ)) × List (Vertex (τ := τ) (Φ := Φ))) :=
  match t with
  | .bind first left (.bind middle _ (.bind second right (.ret _))) =>
    if isLink middle.kind then do
      let xs ← readTheta first.kind (fun j => readBody (left j))
      let ys ← readTheta second.kind (fun j => readBody (right j))
      pure (xs, ys)
    else none

/-- The typed parses recover the two local loops from the vertex labels.
The first loop's two exits and the second entry share `M`. -/
structure View (Φ : Type u) [HasTy Φ τ] (A B K M C J E D : τ)
    (labels : List (Vertex (τ := τ) (Φ := Φ)) × List (Vertex (τ := τ) (Φ := Φ))) where
  first : ExplicitRuntime.Reverse.LoopView Φ [.theta labels.1] A B K M M
  second : ExplicitRuntime.Reverse.LoopView Φ [.theta labels.2] M C J E D

def View.decode {labels : List (Vertex (τ := τ) (Φ := Φ)) × List (Vertex (τ := τ) (Φ := Φ))}
    (view : View Φ A B K M C J E D labels) : Loops Φ A B K M C J E D :=
  ⟨view.first.decode, view.second.decode⟩

/-- A source-free witness for the numbered graph. The wiring certificate
checks all numbered addresses, including the token edges through the
link and the output routing at the second θ. -/
structure Decomposition (g : Graph Φ A M E D) (B K C J : τ) where
  checked : EntryChecked (a := carriedData (First A M)) (b := carriedData (Second M E D)) g.toTerm
  labels : List (Vertex (τ := τ) (Φ := Φ)) × List (Vertex (τ := τ) (Φ := Φ))
  shape : read g.toTerm = some labels
  view : View Φ A B K M C J E D labels
  wiring : graph view.decode = g

abbrev Fibre (g : Graph Φ A M E D) (B K C J : τ) :=
  Σ r : Region Φ, Related A B K M C J E D r g

/-- Recover the flat CFG by reusing the two single-loop parses and the
typed label relocation of the sequential source compiler. -/
def raise {g : Graph Φ A M E D} (d : Decomposition g B K C J) : Fibre g B K C J :=
  let source := region d.view.decode
  ⟨source, Eq.mp (congrArg (Related A B K M C J E D source) d.wiring) (Related.loops d.view.decode)⟩

theorem fibre_inhabited {g : Graph Φ A M E D} (d : Decomposition g B K C J) :
    Nonempty (Fibre g B K C J) :=
  ⟨raise d⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse

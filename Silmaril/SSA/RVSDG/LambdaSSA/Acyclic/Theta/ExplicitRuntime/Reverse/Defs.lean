module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Defs

/-! # Structural decomposition of the numbered acyclic-body θ family -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse

open Isotope.LambdaSSA (Region)
open NestedTheta.ExplicitRuntime (EntryChecked)
open OrderedTheta (carriedData)
open OrderedRuntime.Structured (Instruction)
open TwoBlock.TwoExit (Carrier Pure)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K E D : τ}

/-- Project the primitive labels and region nesting of a checked graph.
Wire addresses and port positions are checked separately by the witness. -/
inductive Vertex (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] : Type u where
  | call {A B : τ} : TwoBlock.Instruction Φ A B → Vertex τ Φ
  | classifier {A X Y : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod X Y) → Vertex τ Φ
  | header {A B E : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod E B) → Vertex τ Φ
  | join {A K D : τ} : TwoBlock.Instruction Φ K (Silmaril.coprod D A) → Vertex τ Φ
  | headerExit : Vertex τ Φ
  | gamma : List (List (Vertex τ Φ)) → Vertex τ Φ
  | theta : List (Vertex τ Φ) → Vertex τ Φ

def primitive : {ins out : Ports (OrderedRuntime.Structured.Ty τ)} →
    Instruction (Pure τ) (Effect Φ) ins out → Vertex τ Φ
  | _, _, .pure .exit => .headerExit
  | _, _, .effect (.acyclic (.call _ p)) => .call p
  | _, _, .effect (.acyclic (.classify _ p)) => .classifier p
  | _, _, .effect (.header p) => .header p
  | _, _, .effect (.join p) => .join p

def vertex : {ins out : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Op Φ) ins out) → (Fin kind.arity → List (Vertex τ Φ)) → Vertex τ Φ
  | _, _, .base (.simple (.ordered _ _ op)), _ => primitive op
  | _, _, .base (.gamma _), children => .gamma (List.ofFn children)
  | _, _, .theta _, children => .theta (children (0 : Fin 1))

/-- Read the generator labels from the actual numbered decoder's term. -/
def read :
    {args outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term (Op Φ) args past sigs outs → List (Vertex τ Φ)
  | _, _, _, _, .ret _ => []
  | _, _, _, _, .bind node children rest =>
    vertex node.kind (fun j => read (children j)) :: read rest

/-- A typed parse of a sequence of generator labels. In the sequence case
the witness supplies the split point and the common payload type. -/
inductive BodyView (Φ : Type u) [HasTy Φ τ] : List (Vertex τ Φ) → τ → τ → Type u where
  | call {A B : τ} (p : TwoBlock.Instruction Φ A B) : BodyView Φ [.call p] A B
  | sequence {A X B : τ} {xs ys : List (Vertex τ Φ)} :
      BodyView Φ xs A X → BodyView Φ ys X B → BodyView Φ (xs ++ ys) A B
  | gamma {A X Y B : τ} {left right : List (Vertex τ Φ)}
      (p : TwoBlock.Instruction Φ A (Silmaril.coprod X Y)) :
      BodyView Φ left X B → BodyView Φ right Y B →
      BodyView Φ [.classifier p, .gamma [left, right]] A B

def BodyView.decode : {xs : List (Vertex τ Φ)} → {A B : τ} → BodyView Φ xs A B → Body Φ A B
  | _, _, _, .call p => .instruction p
  | _, _, _, .sequence left right => .sequence left.decode right.decode
  | _, _, _, .gamma p l r => .choice p l.decode r.decode

/-- The source-free target parse fixes the wrapper and its two ordered arms. -/
inductive LoopView (Φ : Type u) [HasTy Φ τ] : List (Vertex τ Φ) → τ → τ → τ → τ → τ → Type u where
  | loop {A B K E D : τ} {xs : List (Vertex τ Φ)}
      (header : TwoBlock.Instruction Φ A (Silmaril.coprod E B))
      (body : BodyView Φ xs B K) (join : TwoBlock.Instruction Φ K (Silmaril.coprod D A)) :
      LoopView Φ [.theta [.header header, .gamma [[.headerExit], xs ++ [.join join]]]] A B K E D

def LoopView.decode {xs : List (Vertex τ Φ)} : LoopView Φ xs A B K E D → Loop Φ A B K E D
  | .loop header body join => ⟨header, body.decode, join⟩

/-- The view is indexed by labels read from the supplied graph. The last
field certifies its full numbered wiring, including the token edges. -/
structure Decomposition (g : Graph Φ A E D) (B K : τ) where
  checked : EntryChecked (a := carriedData (Carrier A E D)) (b := carriedData (Carrier A E D)) g.toTerm
  view : LoopView Φ (read g.toTerm) A B K E D
  wiring : graph view.decode = g

abbrev Fibre (g : Graph Φ A E D) (B K : τ) :=
  Σ r : Region Φ, Related A B K E D r g

/-- Recover a typed flat CFG by reading the structural view and composing
its typed local blocks, then transport the relation along the wire certificate. -/
def raise {g : Graph Φ A E D} (d : Decomposition g B K) : Fibre g B K :=
  let source := region d.view.decode
  ⟨source, Eq.mp (congrArg (Related A B K E D source) d.wiring) (Related.loop d.view.decode)⟩

theorem fibre_inhabited {g : Graph Φ A E D} (d : Decomposition g B K) : Nonempty (Fibre g B K) :=
  ⟨raise d⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse

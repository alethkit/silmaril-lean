module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Defs

/-! # Compose nested-feedback leaves with the structured CFG translator -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback

open Isotope.LambdaSSA (Region)
open Sequential
open Sequential.Flat.Serial (Code WirePorts Joined payloadData)
open OrderedTheta (carried carriedData)
open OrderedRuntime.Structured (Data Instruction Threaded runtime runtimePort nextRuntime)
open NestedTheta.ExplicitRuntime (Checked EntryChecked)
open NestedTheta.ExplicitRuntime.Splice (append)
open LinearChain.Wiring (newest)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K X Z H U V M Y I J L E D Q R : τ}
variable {ps qs ts sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

namespace Leaf

/-- Add a second external label of the join payload type. The only external
target in the block table is label 2, the first of the two exits. -/
def source (s : NestedFeedback.Loop Φ A B K M) : Flat.Fragment Φ A M M where
  extra := 1
  localTypes := TwoBlock.localTypes A B
  entry := .jump ⟨0,rfl⟩
  blocks i := Fin.cases (motive := fun j =>
    Flat.Block Φ [A,B,M,M] (TwoBlock.localTypes A B j))
    (.call s.enter ⟨1,rfl⟩)
    (fun _ => .choose s.inner
      (.choose s.finish (.jump ⟨2,rfl⟩) (.jump ⟨0,rfl⟩))
      (.jump ⟨1,rfl⟩)) i

theorem source_region (s : NestedFeedback.Loop Φ A B K M) :
    (source s).region = NestedFeedback.region s := by
  apply congrArg (Isotope.LambdaSSA.Region.cfg (.br 0 (.var 0)) 2)
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

def liftInstruction {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} :
    Instruction (NestedFeedback.Pure τ) (NestedFeedback.Effect Φ) ins outs →
      Instruction (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) ins outs
  | .pure op => nomatch op
  | .effect op => .effect (.nested op)

/-- Embed the standalone checked graph while retaining its nested scopes
and every data and token origin. -/
def liftChecked :
    {args outs : Ports (OrderedRuntime.Structured.Ty τ)} → {a : Data args} → {b : Data outs} →
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    {live : Origin (Threaded args) past runtime} →
    {t : NestedTheta.Term (NestedFeedback.Op Φ) (Threaded args) past sigs (Threaded outs)} →
    Checked (NestedFeedback.Pure τ) (NestedFeedback.Effect Φ) a b live t → Wires.Code Φ a b live sigs
  | _, _, _, _, _, _, _, _, .ret live values => ⟨_, .ret live values⟩
  | _, _, _, _, _, _, _, _, .primitive live i o op values rest =>
    ⟨_, .primitive live i o (liftInstruction op) values (liftChecked rest).2⟩
  | _, _, _, _, _, _, _, _, .gamma extra choice live i o values sigs arms rest =>
    ⟨_, .gamma extra choice live i o values sigs (children := fun j => (liftChecked (arms j)).1)
      (fun j => (liftChecked (arms j)).2) (liftChecked rest).2⟩
  | _, _, _, _, _, _, _, _, .theta live i values sigs body rest =>
    ⟨_, .theta live i values sigs (children := fun j => (liftChecked (body j)).1)
      (fun j => (liftChecked (body j)).2) (liftChecked rest).2⟩

def bridge (op : Wires.Effect Φ (carried Q) (carried R)) :
    Wires.Code (past := []) Φ (carriedData Q) (carriedData R) (.arg (runtimePort (carried Q)))
      [Threaded (carried R)] :=
  ⟨_, .primitive (.arg (runtimePort (carried Q))) (carriedData _) (carriedData _) (.effect op)
    (.cons (.arg .head) .nil)
    (.ret (nextRuntime [] (carried R)) (.cons (newest .head []) .nil))⟩

abbrev InnerPorts (A M : τ) := Threaded (carried (NestedFeedback.Carrier A M))
abbrev Sigs (A M : τ) := [InnerPorts A M, InnerPorts A M, WirePorts A M M]

/-- The carrier conversions run outside the existing two θ vertices and
pass the origin of the returned token through the checked splices. -/
def code (s : NestedFeedback.Loop Φ A B K M) : Code Φ A M M A M M (Sigs A M) :=
  append (bridge (Φ := Φ) (.exitNested (A := A) (M := M))).2
    (append (liftChecked (NestedFeedback.Wiring.loop s).2).2
      (bridge (Φ := Φ) (.enterNested (A := A) (M := M))).2).2

end Leaf

/-- The existing structured grammar can appear as a subtree. A single-exit
nested leaf embeds at the homogeneous join interface. The same link and fork
combinators apply recursively on both kinds of leaves. -/
inductive Syntax (Φ : Type u) [HasTy Φ τ] :
    τ → τ → τ → τ → τ → τ → List (Ports (OrderedRuntime.Structured.Ty τ)) → Type u where
  | structured {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      StructuredCFG.Syntax Φ A X Z L E D sigs → Syntax Φ A X Z L E D sigs
  | nested {A B K M : τ} :
      NestedFeedback.Loop Φ A B K M → Syntax Φ A M M A M M (Leaf.Sigs A M)
  | link {A X Z H M I J L E D : τ} {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      Syntax Φ A X Z H M M ps → Syntax Φ M I J L E D qs →
      Syntax Φ A X Z L E D (Joined M I J ps qs)
  | branch {A X Z U V M Y I J L E D : τ} {ps qs ts : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      TwoBlock.Instruction Φ A (ChoiceCarrier M Y) →
      Syntax Φ M M M U M M ps → Syntax Φ Y M M V M M qs → Syntax Φ M I J L E D ts →
      Syntax Φ A X Z L E D (Selection M Y I J ++ ts)

def Syntax.source : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Syntax Φ A X Z L E D sigs → Flat.Fragment Φ A E D
  | _, _, _, _, _, _, _, .structured s => s.source
  | _, _, _, _, _, _, _, .nested s => Leaf.source s
  | _, _, _, _, _, _, _, .link p q => Flat.link p.source q.source
  | _, _, _, _, _, _, _, .branch gate p q tail => Flat.link (Flat.fork p.source q.source gate) tail.source

def Syntax.code : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Syntax Φ A X Z L E D sigs → Code Φ A X Z L E D sigs
  | _, _, _, _, _, _, _, .structured s => s.code
  | _, _, _, _, _, _, _, .nested s => Leaf.code s
  | _, _, _, _, _, _, _, .link p q => Flat.Serial.splice p.code q.code
  | _, _, _, _, _, _, _, .branch gate p q tail => StructuredCFG.Wiring.branch gate p.code q.code tail.code

def Syntax.graph (s : Syntax Φ A X Z L E D sigs) : Flat.Serial.Graph Φ A X Z L E D sigs := s.code.1.toGraph

inductive Related (A X Z L E D : τ) (sigs : List (Ports (OrderedRuntime.Structured.Ty τ))) :
    Region Φ → Flat.Serial.Graph Φ A X Z L E D sigs → Type u where
  | generated (s : Syntax Φ A X Z L E D sigs) : Related A X Z L E D sigs s.source.region s.graph

abbrev Fibre (g : Flat.Serial.Graph Φ A X Z L E D sigs) := Σ r : Region Φ, Related A X Z L E D sigs r g

def lower (s : Syntax Φ A X Z L E D sigs) :
    Σ g, Related A X Z L E D sigs s.source.region g :=
  ⟨s.graph, .generated s⟩

theorem Related.typing {r : Region Φ} {g : Flat.Serial.Graph Φ A X Z L E D sigs}
    (w : Related A X Z L E D sigs r g) : Region.HasType [A] r [E,D] :=
  match w with | .generated s => s.source.typing

def Related.checked {r : Region Φ} {g : Flat.Serial.Graph Φ A X Z L E D sigs}
    (w : Related A X Z L E D sigs r g) :
    EntryChecked (a := payloadData A X Z) (b := payloadData L E D) g.toTerm :=
  match w with | .generated s => s.code.2.collect

/-- A checked graph-side decomposition reconstructs the CFG from the
structured views and a literal numbered wiring equality. -/
structure Decomposition (g : Flat.Serial.Graph Φ A X Z L E D sigs) where
  shape : Syntax Φ A X Z L E D sigs
  wiring : shape.graph = g

def Decomposition.raise {g : Flat.Serial.Graph Φ A X Z L E D sigs} (d : Decomposition g) : Fibre g :=
  ⟨d.shape.source.region, Eq.mp (congrArg (Related A X Z L E D sigs _) d.wiring) (.generated d.shape)⟩

/-- Reuse the standalone nested recognizer's successful match as a leaf view. -/
def ofNested {g : NestedFeedback.Graph Φ A M} (leaf : NestedFeedback.Reverse.Match g) :
    Syntax Φ A M M A M M (Leaf.Sigs A M) :=
  .nested leaf.view.2.2

/-- The cut certifies the full composite graph. Its local views carry no
source CFG. The two local parsers may be run independently. -/
def linkMatches {g : NestedFeedback.Graph Φ A M}
    {h : Flat.Serial.Graph Φ M I J L E D qs} {joint : Flat.Serial.Graph Φ A M M L E D (Joined M I J (Leaf.Sigs A M) qs)}
    (left : NestedFeedback.Reverse.Match g) (right : StructuredCFG.Decomposition h)
    (cut : Flat.Serial.Cut (ofNested left).code right.shape.code joint) : Fibre joint :=
  (⟨.link (ofNested left) (.structured right.shape), cut.wiring⟩ : Decomposition joint).raise

/-- For a supplied cut, parse both graph views and certify the original
joint graph against their checked composition. -/
def recoverLink [DecidableEq τ] [DecidableEq Φ]
    (left : NestedFeedback.Graph Φ A M) (right : Flat.Serial.Graph Φ M I J L E D qs)
    (joint : Flat.Serial.Graph Φ A M M L E D (Joined M I J (Leaf.Sigs A M) qs)) : Option (Fibre joint) := do
  let nested ← NestedFeedback.Reverse.recognize left
  let tail ← StructuredCFG.Reverse.recognize right
  let cut ← Flat.Serial.certifyCut (ofNested nested).code tail.decomposition.shape.code joint
  return linkMatches nested tail.decomposition cut

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback

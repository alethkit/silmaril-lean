module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Check.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Model.Defs

/-! # Serial cuts in checked loop graphs and their flat LambdaSSA regions -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial

open OrderedTheta (carried carriedData)
open OrderedRuntime.Structured (Threaded runtimePort)
open TwoBlock.TwoExit (Carrier enter)
open NestedTheta.ExplicitRuntime (EntryChecked)
open NestedTheta.ExplicitRuntime.Splice (append)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Y H M I J L E D : τ}
variable {ps qs sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

abbrev PayloadPorts (A E D : τ) := carried (Carrier A E D)
abbrev WirePorts (A E D : τ) := Threaded (PayloadPorts A E D)
abbrev payloadData (A E D : τ) := carriedData (Carrier A E D)

/-- `X,Y` describe the input carrier. `L,E,D` describe the last component's
output carrier. The first and last components can have different carriers. -/
abbrev Graph (Φ : Type u) [HasTy Φ τ] (A X Y L E D : τ)
    (sigs : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  NestedTheta.Graph (Wires.Op Φ) (WirePorts A X Y) [] sigs (WirePorts L E D)

abbrev Code (Φ : Type u) [HasTy Φ τ] (A X Y L E D : τ)
    (sigs : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  Wires.Code (past := []) Φ (payloadData A X Y) (payloadData L E D)
    (.arg (runtimePort (PayloadPorts A X Y))) sigs

abbrev Joined (M I J : τ) (ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  ps ++ (WirePorts M I J :: qs)

/-- Redirect both producer exits, which carry the same data type, into the
consumer carrier. Two checked splices wire the data and token as one tuple. -/
def splice (p : Code Φ A X Y H M M ps) (q : Code Φ M I J L E D qs) :
    Code Φ A X Y L E D (Joined M I J ps qs) :=
  let tail := append q.2 (Numbered.connector (Φ := Φ) (I := H) (M := M) (E := I) (D := J)).2
  append tail.2 p.2

def joinedGraph (p : Code Φ A X Y H M M ps) (q : Code Φ M I J L E D qs) :
    Graph Φ A X Y L E D (Joined M I J ps qs) :=
  (splice p q).1.toGraph

/-- A cut is an exact equality of typed numbered graphs. It checks both
crossing data and token uses, all relocated references, and child scopes. -/
structure Cut (p : Code Φ A X Y H M M ps) (q : Code Φ M I J L E D qs)
    (g : Graph Φ A X Y L E D (Joined M I J ps qs)) : Type u where
  wiring : joinedGraph p q = g

def Cut.checked
    {p : Code Φ A X Y H M M ps} {q : Code Φ M I J L E D qs}
    {g : Graph Φ A X Y L E D (Joined M I J ps qs)} (cut : Cut p q g) :
    EntryChecked (a := payloadData A X Y) (b := payloadData L E D) g.toTerm :=
  cut.wiring ▸ (splice p q).2.collect

/-- Check one supplied cut and its two components against the actual table. -/
def certifyCut [DecidableEq τ] [DecidableEq Φ]
    (p : Code Φ A X Y H M M ps) (q : Code Φ M I J L E D qs)
    (g : Graph Φ A X Y L E D (Joined M I J ps qs)) : Option (Cut p q g) :=
  letI : DecidableEq (PortType τ PUnit) := inferInstance
  letI := NestedTheta.Equality.decideGraph (Numbered.Recognize.opcodeCode (τ := τ) (Φ := Φ)) (joinedGraph p q) g
  if same : joinedGraph p q = g then some ⟨same⟩ else none

/-- A nonempty typed serial composition. A leaf uses the existing structured
loop. A cut can attach two composites of any size with matching payloads. -/
inductive Spine (Φ : Type u) [HasTy Φ τ] :
    τ → τ → τ → τ → τ → τ → List (Ports (OrderedRuntime.Structured.Ty τ)) → Type u where
  | loop {A B K E D : τ} (s : Loop Φ A B K E D) :
      Spine Φ A E D A E D [WirePorts A E D]
  | link {A X Y H M I J L E D : τ} {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      Spine Φ A X Y H M M ps → Spine Φ M I J L E D qs → Spine Φ A X Y L E D (Joined M I J ps qs)

/-- Each cut emits a single flat block table with freshly relocated labels. -/
def Spine.source : {A X Y L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Spine Φ A X Y L E D sigs → Fragment Φ A E D
  | _, _, _, _, _, _, _, .loop s => Fragment.loop s
  | _, _, _, _, _, _, _, .link p q => Flat.link p.source q.source

def Spine.code : {A X Y L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Spine Φ A X Y L E D sigs → Code Φ A X Y L E D sigs
  | _, _, _, _, _, _, _, .loop s => Wires.liftChecked (ExplicitRuntime.Wiring.loop s).2
  | _, _, _, _, _, _, _, .link p q => splice p.code q.code

def Spine.graph (s : Spine Φ A X Y L E D sigs) : Graph Φ A X Y L E D sigs :=
  s.code.1.toGraph

/-- Obtain a leaf from an existing source-free local parse and wiring
certificate. The shared dialect leaf is the lift of its decoded loop. -/
def Spine.ofLoop {B K : τ} {g : ExplicitRuntime.Graph Φ A E D}
    (d : ExplicitRuntime.Reverse.Decomposition g B K) :
    Spine Φ A E D A E D [WirePorts A E D] :=
  .loop d.view.decode

/-- A supplied structural decomposition. The source is reconstructed from
the leaves and cuts, and is absent from the certificate's fields. -/
structure Decomposition (g : Graph Φ A X Y L E D sigs) where
  spine : Spine Φ A X Y L E D sigs
  wiring : spine.graph = g

def Spine.decomposition (s : Spine Φ A X Y L E D sigs) : Decomposition s.graph :=
  ⟨s, rfl⟩

def Decomposition.recover {g : Graph Φ A X Y L E D sigs} (d : Decomposition g) : Fragment Φ A E D :=
  d.spine.source

def Decomposition.checked {g : Graph Φ A X Y L E D sigs} (d : Decomposition g) :
    EntryChecked (a := payloadData A X Y) (b := payloadData L E D) g.toTerm :=
  d.wiring ▸ d.spine.code.2.collect

/-- Recover a composite certificate from the two local certificates and an
independently checked cut. No source region is needed for this operation. -/
def Decomposition.link
    {left : Graph Φ A X Y H M M ps} {right : Graph Φ M I J L E D qs}
    {g : Graph Φ A X Y L E D (Joined M I J ps qs)}
    (p : Decomposition left) (q : Decomposition right) (cut : Cut p.spine.code q.spine.code g) :
    Decomposition g :=
  ⟨.link p.spine q.spine, cut.wiring⟩

section Model

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open OrderedTheta (point)

variable {ε σ : Type u} [HasEff Φ ε] [Bot ε] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

noncomputable def observe (g : Graph Φ A X Y L E D sigs) (input : TyDen A) (initial : σ) :=
  NestedTheta.Partial.observe (Wires.wireModel (ε := ε)) g
    (point (enter (A := A) (C := X) (D := Y) input) initial)

def returns (g : Graph Φ A X Y L E D sigs) (input : TyDen A) (initial : σ)
    (exit : LabelDen [E,D]) (final : σ) : Prop :=
  NestedTheta.Partial.returns (Wires.wireModel (ε := ε)) g
    (point (enter (A := A) (C := X) (D := Y) input) initial)
    (ExplicitRuntime.exitTuple (A := L) (exit, final))

/-- A model-level observation law, for use as a premise when composing
already admitted components. The cut certificate is a separate syntax test. -/
def Agrees (source : Fragment Φ A E D) (g : Graph Φ A X Y L E D sigs) : Prop :=
  ∀ (env : Env [A]) (initial : σ),
    observe (ε := ε) g env.2 initial = Part.map (ExplicitRuntime.exitTuple (A := L))
      ((Region.denote (ε := ε) (m := StateT σ Part.{u}) source.typing env).run initial)

end Model

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial

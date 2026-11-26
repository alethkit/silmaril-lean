module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Fork.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Defs

/-! # Structured composition of flat LambdaSSA regions and checked RVSDG regions -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG

open Isotope.LambdaSSA (Region)
open Sequential
open Sequential.Flat.Serial (Code WirePorts)
open OrderedTheta (carried carriedData results resultData)
open OrderedRuntime.Structured (Threaded runtimePort nextRuntime)
open TwoBlock.TwoExit (Carrier)
open NestedTheta.ExplicitRuntime (EntryChecked)
open NestedTheta.ExplicitRuntime.Splice (append)
open LinearChain.Wiring (newest)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z H U V M Y I J L E D : τ}
variable {ps qs ts sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

abbrev ChoiceCarrier (M Y : τ) := Carrier Y M M
abbrev Selection (M Y I J : τ) :=
  [Threaded (results (ChoiceCarrier M Y)), WirePorts M I J]

namespace Wiring

/-- The left injection of the classifier already carries one of two
payloads of type M. Route that payload to the left child's entry. -/
def leftArm (p : Code Φ M M M U M M ps) :
    Code Φ Y M M M I J (WirePorts M M M :: (ps ++ [WirePorts M I J])) :=
  let enter := Flat.Numbered.connector (Φ := Φ) (I := Y) (M := M) (E := M) (D := M)
  let leave := Flat.Numbered.connector (Φ := Φ) (I := U) (M := M) (E := I) (D := J)
  append leave.2 (append p.2 enter.2).2

def rightArm (q : Code Φ Y M M V M M qs) :
    Code Φ Y M M M I J (qs ++ [WirePorts M I J]) :=
  append (Flat.Numbered.connector (Φ := Φ) (I := V) (M := M) (E := I) (D := J)).2 q.2

/-- The classifier reads the active input injection of the standard
serial carrier. γ receives the new token and passes it to one child. -/
def select (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : Code Φ M M M U M M ps) (q : Code Φ Y M M V M M qs) :
    Code Φ A X Z M I J (Selection M Y I J) :=
  let classified := results (ChoiceCarrier M Y)
  let joined := carried (Carrier M I J)
  let before := [Threaded classified]
  let arms j := Fin.cases (motive := fun (_ : Fin 2) => Σ sigs, Code Φ Y M M M I J sigs)
    ⟨_, leftArm p⟩ (fun _ => ⟨_, rightArm q⟩) j
  ⟨_, .primitive (.arg (runtimePort (carried (Carrier A X Z)))) (carriedData _) (resultData _)
    (.effect (.loop (.acyclic (.classify .right gate)))) (.cons (.arg .head) .nil) <|
      .gamma 0 (newest .head []) (nextRuntime [] classified) (carriedData (ChoiceCarrier M Y))
        (carriedData (Carrier M I J)) (.cons (newest (.tail .head) []) .nil) (fun j => (arms j).1)
        (children := fun j => (arms j).2.1) (fun j => (arms j).2.2)
        (.ret (nextRuntime before joined) (.cons (newest .head before) .nil))⟩

def branch (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : Code Φ M M M U M M ps) (q : Code Φ Y M M V M M qs) (tail : Code Φ M I J L E D ts) :
    Code Φ A X Z L E D (Selection M Y I J ++ ts) :=
  append tail.2 (select gate p q).2

end Wiring

/-- A finite grammar with loop leaves. Each arm and the shared continuation
can themselves be structured, as can either side of a serial link.
Every internal join consumes two labels of the same payload sort. -/
inductive Syntax (Φ : Type u) [HasTy Φ τ] :
    τ → τ → τ → τ → τ → τ → List (Ports (OrderedRuntime.Structured.Ty τ)) → Type u where
  | loop {A B K E D : τ} (s : Loop Φ A B K E D) :
      Syntax Φ A E D A E D [WirePorts A E D]
  | link {A X Z H M I J L E D : τ} {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      Syntax Φ A X Z H M M ps → Syntax Φ M I J L E D qs →
      Syntax Φ A X Z L E D (Flat.Serial.Joined M I J ps qs)
  | branch {A X Z U V M Y I J L E D : τ} {ps qs ts : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      TwoBlock.Instruction Φ A (ChoiceCarrier M Y) →
      Syntax Φ M M M U M M ps → Syntax Φ Y M M V M M qs → Syntax Φ M I J L E D ts →
      Syntax Φ A X Z L E D (Selection M Y I J ++ ts)

/-- Relocate each subtree into one flat table, with a single shared entry
for the continuation after each fork. -/
def Syntax.source : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Syntax Φ A X Z L E D sigs → Flat.Fragment Φ A E D
  | _, _, _, _, _, _, _, .loop s => .loop s
  | _, _, _, _, _, _, _, .link p q => Flat.link p.source q.source
  | _, _, _, _, _, _, _, .branch gate p q tail => Flat.link (Flat.fork p.source q.source gate) tail.source

def Syntax.code : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Syntax Φ A X Z L E D sigs → Code Φ A X Z L E D sigs
  | _, _, _, _, _, _, _, .loop s => (Flat.Serial.Spine.loop s).code
  | _, _, _, _, _, _, _, .link p q => Flat.Serial.splice p.code q.code
  | _, _, _, _, _, _, _, .branch gate p q tail => Wiring.branch gate p.code q.code tail.code

def Syntax.graph (s : Syntax Φ A X Z L E D sigs) : Flat.Serial.Graph Φ A X Z L E D sigs := s.code.1.toGraph

inductive Related (A X Z L E D : τ) (sigs : List (Ports (OrderedRuntime.Structured.Ty τ))) :
    Region Φ → Flat.Serial.Graph Φ A X Z L E D sigs → Type u where
  | generated (s : Syntax Φ A X Z L E D sigs) : Related A X Z L E D sigs s.source.region s.graph

def lower (s : Syntax Φ A X Z L E D sigs) :
    Σ g, Related A X Z L E D sigs s.source.region g :=
  ⟨s.graph, .generated s⟩

theorem Related.typing {r : Region Φ} {g : Flat.Serial.Graph Φ A X Z L E D sigs}
    (w : Related A X Z L E D sigs r g) : Region.HasType [A] r [E,D] :=
  match w with | .generated s => s.source.typing

def Related.checked {r : Region Φ} {g : Flat.Serial.Graph Φ A X Z L E D sigs}
    (w : Related A X Z L E D sigs r g) :
    EntryChecked (a := Flat.Serial.payloadData A X Z) (b := Flat.Serial.payloadData L E D) g.toTerm :=
  match w with | .generated s => s.code.2.collect

/-- The supplied structural decomposition contains only the grammar and
numbered wiring, and yields a flat CFG by construction. -/
structure Decomposition (g : Flat.Serial.Graph Φ A X Z L E D sigs) where
  shape : Syntax Φ A X Z L E D sigs
  wiring : shape.graph = g

def raise {g : Flat.Serial.Graph Φ A X Z L E D sigs} (d : Decomposition g) :
    Σ r : Region Φ, Related A X Z L E D sigs r g :=
  ⟨d.shape.source.region, Eq.mp (congrArg (Related A X Z L E D sigs _) d.wiring) (.generated d.shape)⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG

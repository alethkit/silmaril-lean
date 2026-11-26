module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Defs

/-! # Read the actual numbered serial layout and certify the reconstructed spine -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize

open Wires.Reverse (Vertex readBody)
open Numbered.Recognize (budget RightAssociated)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Y L E D : τ}
variable {args outs : Ports (OrderedRuntime.Structured.Ty τ)}
variable {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- A θ supplies its local label tree and a recursion bound from that very
child. A connector supplies the types of the handoff and next entry carrier. -/
inductive Mark (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] where
  | loop (fuel : Nat) (labels : List (Vertex (τ := τ) (Φ := Φ)))
  | cut (carry payload left right : τ)

def connectorMark : {ins out : Ports (OrderedRuntime.Structured.Ty τ)} →
    Wires.Effect Φ ins out → Option (Mark τ Φ)
  | _, _, .link (A := h) (M := m) (E := i) (D := j) => some (.cut h m i j)
  | _, _, _ => none

def mark : {ins out : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Wires.Op Φ) ins out) →
    {childSigs : Fin kind.arity → List (Ports (OrderedRuntime.Structured.Ty τ))} →
    ((j : Fin kind.arity) → NestedTheta.Term (Wires.Op Φ) kind.entry [] (childSigs j) kind.exit) →
    Option (Mark τ Φ)
  | _, _, .theta _, _, children => do
    let body := children (0 : Fin 1)
    return .loop (budget body) [ExplicitRuntime.Reverse.Vertex.theta (← readBody body)]
  | _, _, .base (.simple (.ordered _ _ (.effect op))), _, _ => connectorMark op
  | _, _, _, _, _ => none

/-- Scan outer positions in order. Each leaf's body uses its own numbering
and scope. The subsequent exact comparison checks every wire origin. -/
def scan : {args outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term (Wires.Op Φ) args past sigs outs → Option (List (Mark τ Φ))
  | _, _, _, _, .ret _ => some []
  | _, _, _, _, .bind node children rest => do
    let head ← mark node.kind children
    return head :: (← scan rest)

structure Output (τ : Type u) where
  carry : τ
  left : τ
  right : τ
  sigs : List (Ports (OrderedRuntime.Structured.Ty τ))
  deriving DecidableEq

abbrev Parsed (Φ : Type u) [HasTy Φ τ] (A X Y : τ) :=
  Σ o : Output τ, Spine Φ A X Y o.carry o.left o.right o.sigs

def pack (s : Spine Φ A X Y L E D sigs) : Parsed Φ A X Y := ⟨⟨L, E, D, sigs⟩, s⟩

/-- The scanner reconstructs a left fold of the ordered leaves. Bodies
at each leaf use the right-associated form of the shared label parser. -/
inductive LeftAssociated : {A X Y L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Spine Φ A X Y L E D sigs → Prop where
  | single {A B K E D : τ} (s : Loop Φ A B K E D) :
      RightAssociated s.body → LeftAssociated (.loop s)
  | push {A X Y H M B K E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
      {first : Spine Φ A X Y H M M sigs} (next : Loop Φ M B K E D) :
      LeftAssociated first → RightAssociated next.body → LeftAssociated (.link first (.loop next))

variable [DecidableEq τ]

/-- Read one connector and the next θ. The two producer exits must have
the connector's handoff type, and the producer carrier must match its tag. -/
def extend : Parsed Φ A X Y → List (Mark τ Φ) → Option (Parsed Φ A X Y)
  | parsed, [] => some parsed
  | ⟨⟨carry, left, right, _⟩, prior⟩, .cut h m i j :: .loop fuel labels :: rest =>
    if hCarry : carry = h then
      if hLeft : left = m then
        if hRight : right = m then do
          let ⟨_, _, next⟩ ← Numbered.Recognize.loop fuel m i j labels
          let producer : Spine Φ A X Y h m m _ := hCarry ▸ hLeft ▸ hRight ▸ prior
          extend (pack (.link producer (.loop next))) rest
        else none
      else none
    else none
  | _, _ => none

def parse : List (Mark τ Φ) → Option (Parsed Φ A X Y)
  | .loop fuel labels :: tail => do
    let ⟨_, _, first⟩ ← Numbered.Recognize.loop fuel A X Y labels
    extend (pack (.loop first)) tail
  | _ => none

/-- The candidate comes solely from the actual table and its typed interface. -/
def candidate (g : Graph Φ A X Y L E D sigs) : Option (Spine Φ A X Y L E D sigs) := do
  let ⟨o, s⟩ ← (parse (← scan g.toTerm) : Option (Parsed Φ A X Y))
  if eq : o = (⟨L, E, D, sigs⟩ : Output τ) then
    some (Eq.mp (congrArg (fun ix => Spine Φ A X Y ix.carry ix.left ix.right ix.sigs) eq) s)
  else none

variable [DecidableEq Φ]

/-- On a nontrivial spine, the final cut compares the entire reconstructed
table, which includes all earlier cuts. A single leaf needs just graph equality. -/
def certify : {A X Y L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    (g : Graph Φ A X Y L E D sigs) → Spine Φ A X Y L E D sigs → Option (Decomposition g)
  | _, _, _, _, _, _, _, g, .loop s =>
    let plan := Spine.loop s
    letI := NestedTheta.Equality.decideGraph (Numbered.Recognize.opcodeCode (τ := τ) (Φ := Φ)) plan.graph g
    if same : plan.graph = g then some ⟨plan, same⟩ else none
  | _, _, _, _, _, _, _, g, .link p q => (certifyCut p.code q.code g).map fun cut => ⟨.link p q, cut.wiring⟩

def recognize (g : Graph Φ A X Y L E D sigs) : Option (Decomposition g) :=
  (candidate g).bind (certify g)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize

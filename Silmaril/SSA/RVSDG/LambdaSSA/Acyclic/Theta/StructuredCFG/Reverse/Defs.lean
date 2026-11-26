module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Defs

/-! # Parse the emitted fork and serial layout before checking every wire -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse

open Isotope.LambdaSSA (Region)
open Sequential
open Sequential.Flat.Serial (WirePorts Joined)
open Sequential.Flat.Serial.Recognize (Mark Output mark)
open Sequential.Flat.Numbered.Recognize (opcodeCode RightAssociated)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Z H M Y I J U V L E D : τ}
variable {ps qs ts sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- A serial link starts with one loop and associates to the right.
A fork owns its remaining continuation. Its two arms normalize independently. -/
inductive Normal (Φ : Type u) [HasTy Φ τ] :
    τ → τ → τ → τ → τ → τ → List (Ports (OrderedRuntime.Structured.Ty τ)) → Type u where
  | loop {A B K E D : τ} (s : Loop Φ A B K E D) :
      Normal Φ A E D A E D [WirePorts A E D]
  | link {A B K M I J L E D : τ} {qs : List (Ports (OrderedRuntime.Structured.Ty τ))}
      (first : Loop Φ A B K M M) (rest : Normal Φ M I J L E D qs) :
      Normal Φ A M M L E D (Joined M I J [WirePorts A M M] qs)
  | branch {A X Z U V M Y I J L E D : τ} {ps qs ts : List (Ports (OrderedRuntime.Structured.Ty τ))} :
      TwoBlock.Instruction Φ A (ChoiceCarrier M Y) →
      Normal Φ M M M U M M ps → Normal Φ Y M M V M M qs → Normal Φ M I J L E D ts →
      Normal Φ A X Z L E D (Selection M Y I J ++ ts)

def Normal.toSyntax : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Normal Φ A X Z L E D sigs → Syntax Φ A X Z L E D sigs
  | _, _, _, _, _, _, _, .loop s => .loop s
  | _, _, _, _, _, _, _, .link s rest => .link (.loop s) rest.toSyntax
  | _, _, _, _, _, _, _, .branch gate left right rest =>
    .branch gate left.toSyntax right.toSyntax rest.toSyntax

/-- The local θ parser also uses right association for instruction sequences. -/
def Supported : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Normal Φ A X Z L E D sigs → Prop
  | _, _, _, _, _, _, _, .loop s => RightAssociated s.body
  | _, _, _, _, _, _, _, .link s rest => RightAssociated s.body ∧ Supported rest
  | _, _, _, _, _, _, _, .branch _ left right rest => Supported left ∧ Supported right ∧ Supported rest

inductive Entry (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] where
  | atom (mark : Mark τ Φ)
  | classifier {A X Y : τ} (op : TwoBlock.Instruction Φ A (Silmaril.coprod X Y))
  | fork (left right : List (Entry τ Φ))

abbrev Layout (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] := List (Entry τ Φ)

variable {args outs ins : Ports (OrderedRuntime.Structured.Ty τ)} {past : List (Ports (OrderedRuntime.Structured.Ty τ))}

def readEntry : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Wires.Op Φ) ins outs) →
    (Fin kind.arity → Option (Layout τ Φ)) → Option (Mark τ Φ) → Option (Entry τ Φ)
  | _, _, .base (.gamma 0), children, _ => do
    return .fork (← children (0 : Fin 2)) (← children (1 : Fin 2))
  | _, _, kind@(.base (.simple _)), _, atom =>
    match Wires.Reverse.readKind kind (fun _ => none) with
    | some (.classifier op) => some (.classifier op)
    | _ => .atom <$> atom
  | _, _, _, _, atom => .atom <$> atom

/-- Keep the nested γ child tables and reuse the serial reader for θ and connector nodes.
Numbered operands and returns are checked at certification. -/
def scan : {args outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term (Wires.Op Φ) args past sigs outs → Option (Layout τ Φ)
  | _, _, _, _, .ret _ => some []
  | _, _, _, _, .bind node children rest => do
    let first ← readEntry node.kind (fun i => scan (children i)) (mark node.kind children)
    return first :: (← scan rest)

/-- The available recursion depth is computed from the graph's actual label layout. -/
def weight : Layout τ Φ → Nat
  | [] => 0
  | .fork left right :: tail => weight left + weight right + weight tail + 1
  | _ :: tail => weight tail + 1
termination_by marks => sizeOf marks
decreasing_by all_goals (simp_wf; omega)

structure CutTag (τ : Type u) where
  carry : τ
  left : τ
  right : τ

/-- The final connector in each γ region converts the arm exit to the
common entry carrier. Its mark also identifies the arm's last carrier. -/
def splitArm (arm : Layout τ Φ) : Option (CutTag τ × Layout τ Φ) :=
  match arm.reverse with
  | .atom (.cut carry _ left right) :: reversed =>
    some (⟨carry, left, right⟩, reversed.reverse)
  | _ => none

abbrev Parsed (Φ : Type u) [HasTy Φ τ] (A X Z : τ) :=
  Σ out : Output τ, Normal Φ A X Z out.carry out.left out.right out.sigs

def pack (n : Normal Φ A X Z L E D sigs) : Parsed Φ A X Z := ⟨⟨L,E,D,sigs⟩, n⟩

variable [DecidableEq τ]

def expect (parsed : Parsed Φ A X Z) (carry e d : τ) :
    Option (Σ sigs, Normal Φ A X Z carry e d sigs) :=
  let ⟨out, n⟩ := parsed
  if hc : out.carry = carry then
    if he : out.left = e then
      if hd : out.right = d then some ⟨out.sigs, hc ▸ he ▸ hd ▸ n⟩ else none
    else none
  else none

def parse : Nat → (A X Z : τ) → Layout τ Φ → Option (Parsed Φ A X Z)
  | 0, _, _, _, _ => none
  | _ + 1, A, X, Z, [.atom (.loop steps labels)] => do
    let ⟨_, _, s⟩ ← Flat.Numbered.Recognize.loop steps A X Z labels
    return pack (.loop s)
  | fuel + 1, A, X, Z, .atom (.loop steps labels) :: .atom (.cut _ m i j) :: rest =>
    if hl : X = m then
      if hr : Z = m then do
        let ⟨_, _, first⟩ ← Flat.Numbered.Recognize.loop steps A m m labels
        let ⟨_, next⟩ ← parse fuel m i j rest
        let result : Parsed Φ A m m := pack (.link first next)
        return hl.symm ▸ hr.symm ▸ result
      else none
    else none
  | fuel + 1, A, _, _,
      .classifier (A := a) (X := x) (Y := y) op ::
        .fork (.atom (.cut Y M _ _) :: left) right :: rest =>
    if ha : a = A then
      if ho : Silmaril.coprod x y = ChoiceCarrier M Y then do
        let (leftExit, leftMarks) ← splitArm left
        let (rightExit, rightMarks) ← splitArm right
        let ⟨_, l⟩ ← expect (← parse fuel M M M leftMarks) leftExit.carry M M
        let ⟨_, r⟩ ← expect (← parse fuel Y M M rightMarks) rightExit.carry M M
        let ⟨_, next⟩ ← parse fuel M leftExit.left leftExit.right rest
        let gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y) := ha ▸ ho ▸ op
        return pack (.branch gate l r next)
      else none
    else none
  | _, _, _, _, _ => none

def decodeLayout (labels : Layout τ Φ) : Option (Normal Φ A X Z L E D sigs) := do
  let ⟨out, n⟩ ← parse (weight labels) A X Z labels
  if eq : out = (⟨L,E,D,sigs⟩ : Output τ) then
    some (Eq.mp (congrArg (fun ix => Normal Φ A X Z ix.carry ix.left ix.right ix.sigs) eq) n)
  else none

def candidate (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (Normal Φ A X Z L E D sigs) :=
  (scan g.toTerm).bind decodeLayout

structure Match (g : Flat.Serial.Graph Φ A X Z L E D sigs) where
  view : Normal Φ A X Z L E D sigs
  wiring : view.toSyntax.graph = g

def Match.decomposition {g : Flat.Serial.Graph Φ A X Z L E D sigs} (m : Match g) : Decomposition g :=
  ⟨m.view.toSyntax, m.wiring⟩

variable [DecidableEq Φ]

/-- Check all graph fields recursively, including child scopes, selectors,
data operands, results and live-token addresses. -/
def certify (g : Flat.Serial.Graph Φ A X Z L E D sigs) (n : Normal Φ A X Z L E D sigs) :
    Option (Match g) :=
  letI := NestedTheta.Equality.decideGraph (opcodeCode (τ := τ) (Φ := Φ)) n.toSyntax.graph g
  if eq : n.toSyntax.graph = g then some ⟨n, eq⟩ else none

def recognize (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (Match g) :=
  (candidate g).bind (certify g)

abbrev Fibre (g : Flat.Serial.Graph Φ A X Z L E D sigs) :=
  Σ r : Region Φ, Related A X Z L E D sigs r g

/-- Compute a flat CFG and the checked relation witness from the graph. -/
def recover (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (Fibre g) :=
  (recognize g).map (raise ∘ Match.decomposition)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse

module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Defs

/-! # A tail-tested λSSA CFG carrying the whole heap -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA

open SeaOfNodes.Loop (Incoming)
open Memory.Diamond.LambdaSSA
  (Atom Code Instruction Opcode Routing Schedule guardCode inputEnv packet prepend schedule shift wordCode)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

variable {args : List ValueSort} {cells : Nat}

abbrev inputContext (args : List ValueSort) : List Code := args.map Silmaril.Ty.base

def headerSchedule (g : Graph args) : Schedule args :=
  schedule g.body (Routing.weaken .unit (Routing.entry args))

def comparison (g : Graph args) : Tm Opcode :=
  .op .equalWords (.pair (.var (headerSchedule g).result.val) (.var ((headerSchedule g).inputRef g.stop).val))

def unitArgs {context : List Code} : PhiView.Arguments context [] :=
  fun i => i.elim0

def exitArgs (g : Graph args) : PhiView.Arguments (.unit :: guardCode :: (headerSchedule g).context) [wordCode] :=
  fun i => Fin.cases (shift .unit (shift guardCode (headerSchedule g).result)) (fun j => j.elim0) i

/-- The preheader and the false successor of the tail test both reach
header zero. A true test exits with the returned word. -/
def terminators (g : Graph args) : Incoming → Terminator Opcode
  | .entry => .br 0 .unit
  | .backedge =>
    .case (.var 0) (.br 1 (PhiView.packTerm (exitArgs g))) (.br 0 .unit)

def sourceTyping (g : Graph args) : PhiView.SourceTyping (τ := Code) (terminators g) where
  context
    | .entry => inputContext args
    | .backedge => guardCode :: (headerSchedule g).context
  cases
    | .entry => .jump
    | .backedge => .case (A := .unit) (B := .unit) (.var (i := 0) rfl) .jump .jump

def parameters : Nat → List Code
  | 1 => [wordCode]
  | _ => []

def blockArgs (g : Graph args) : PhiView.BlockArgs (sourceTyping g) parameters
  | ⟨.entry, .jump⟩ => ⟨unitArgs, rfl⟩
  | ⟨.backedge, .left .jump⟩ => ⟨exitArgs g, rfl⟩
  | ⟨.backedge, .right .jump⟩ => ⟨unitArgs, rfl⟩

def phiView (g : Graph args) : PhiView.View (sourceTyping g) parameters :=
  PhiView.ofBlockArgs (blockArgs g)

def edge (g : Graph args) : Incoming → PhiView.EdgeOcc (terminators g)
  | .entry => ⟨.entry, .jump⟩
  | .backedge => ⟨.backedge, .right .jump⟩

def exitEdge (g : Graph args) : PhiView.EdgeOcc (terminators g) := ⟨.backedge, .left .jump⟩

def transfer {g : Graph args} (occurrence : PhiView.EdgeOcc (terminators g)) : Region Opcode :=
  .br occurrence.target occurrence.argument

def preheader (g : Graph args) : Region Opcode := transfer (edge g .entry)

/-- Run the ordered body once, then test its result in the current heap.
The backedge transfers unit and forwards that heap to the next activation. -/
def header (g : Graph args) : Region Opcode :=
  prepend (headerSchedule g).statements
    (.let₁ (comparison g) (.case (.var 0) (transfer (exitEdge g)) (transfer (edge g .backedge))))

def blocks (g : Graph args) : Fin 1 → Region Opcode := fun _ => header g

def lower (g : Graph args) : Region Opcode := .cfg (preheader g) 1 (blocks g)

abbrev Activation (g : Graph args) (input : Tuple (Val cells) args) :=
  Semantics.Region.Eval (Instruction cells) (extend (inputEnv input) .unit) (header g)

/-- Count actual header evaluations, one per taken backedge plus the exit activation. -/
inductive FollowAfter (g : Graph args) (input : Tuple (Val cells) args) :
    Nat → Heap cells → Word → Heap cells → Prop where
  | exit {heap final : Heap cells} {word : Word}
      (run : Activation g input heap 1 (packet word) final) :
      FollowAfter g input 0 heap word final
  | backedge {heap next final : Heap cells} {count : Nat} {word : Word}
      (run : Activation g input heap 0 Value.unit next)
      (rest : FollowAfter g input count next word final) :
      FollowAfter g input (count + 1) heap word final

end Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA

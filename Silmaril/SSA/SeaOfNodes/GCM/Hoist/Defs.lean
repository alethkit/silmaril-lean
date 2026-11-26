module

public import Silmaril.SSA.SeaOfNodes.GCM.Discovery.Defs

/-! # Checked hoisting of one pure producer across a typed control diamond -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Hoist

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Frame Terminator)
open Silmaril.MLIR.Pure (Eval Operands OpSignature i1)

inductive Label (arg out : Width) (hoisted : Bool) : List Width → Type where
  | left : Label arg out hoisted (if hoisted then [arg, out, out] else [arg, out])
  | right : Label arg out hoisted [out, out]
  | join : Label arg out hoisted [out, out]

/-- This shape fixes the use footprint. Entry binds the source of the unary
producer's operand and sends it to the true arm. Each arm supplies one
result and an independent payload to the join. -/
structure Diamond (Op : OpSignature) (Input : List Width) (arg out : Width) where
  seedTypes : List Width
  seed : Op seedTypes arg
  seedOperands : Operands Input seedTypes
  producer : Op [arg] out
  selector : Var Input i1
  fallback : Var Input out
  leftExtra : Var Input out
  rightExtra : Var Input out

variable {Op : OpSignature} {Input : List Width} {arg out : Width} {Γ : List Width}

def forward {hoisted : Bool} (result extra : Var Γ out) :
    Block Op (Label arg out hoisted) Γ [out, out] :=
  .terminator (.br ⟨.join, .cons result (.cons extra .nil)⟩)

def Diamond.before (g : Diamond Op Input arg out) : Cfg Op (Label arg out false) Input [out, out] where
  entry := .letOp g.seed g.seedOperands (.terminator (.condBr (.there g.selector)
    ⟨.left, .cons .here (.cons (.there g.leftExtra) .nil)⟩
    ⟨.right, .cons (.there g.fallback) (.cons (.there g.rightExtra) .nil)⟩))
  block
    | .left => .letOp g.producer (.cons .here .nil) (forward .here (.there (.there .here)))
    | .right => forward .here (.there .here)
    | .join => .terminator (.ret (.cons .here (.cons (.there .here) .nil)))

/-- Move the binding after the seed. Append its result to the true edge's
arguments, and forward it from the true arm without recomputation. -/
def Diamond.after (g : Diamond Op Input arg out) : Cfg Op (Label arg out true) Input [out, out] where
  entry := .letOp g.seed g.seedOperands (.letOp g.producer (.cons .here .nil)
    (.terminator (.condBr (.there (.there g.selector))
      ⟨.left, .cons (.there .here) (.cons (.there (.there g.leftExtra)) (.cons .here .nil))⟩
      ⟨.right, .cons (.there (.there g.fallback)) (.cons (.there (.there g.rightExtra)) .nil)⟩)))
  block
    | .left => forward (.there (.there .here)) (.there .here)
    | .right => forward .here (.there .here)
    | .join => .terminator (.ret (.cons .here (.cons (.there .here) .nil)))

def leftId : BlockId (Label arg out false) := some ⟨_, .left⟩

def entryCut : Point (Label arg out false) := ⟨none, 1⟩

/-- The true arm's input used by the producer comes from the seed at entry. -/
def operandSites : List (Point (Label arg out false)) := [entryCut]

/-- The producer's sole use is argument zero on the left-to-join occurrence. -/
def useSites : List (Use (Label arg out false)) := [.phi leftId .jump 0]

def blocks : List (Target (Label arg out false)) := [⟨_, .left⟩, ⟨_, .right⟩, ⟨_, .join⟩]

/-- This emitter supports the entry cut after the seed. The actual source
CFG and fixed use footprint are inputs to the existing placement checker. -/
def Diamond.hoistAt? (g : Diamond Op Input arg out) (tree : DominatorTree g.before)
    (cut : Point (Label arg out false)) : Option (Cfg Op (Label arg out true) Input [out, out]) :=
  if checkPlacement tree operandSites useSites cut && (cut.block.isNone && cut.cut == (entryCut (arg := arg) (out := out)).cut) then
    some g.after
  else none

/-- Discover a cut in the source CFG, then emit the rewrite at that cut. -/
def Diamond.pickAndHoist? (g : Diamond Op Input arg out) (tree : DominatorTree g.before) :
    Option (Point (Label arg out false) × Cfg Op (Label arg out true) Input [out, out]) := do
  let cut ← discoverPlacement tree blocks operandSites useSites
  let emitted ← g.hoistAt? tree cut
  pure (cut, emitted)

def Diamond.seedValue (g : Diamond Op Input arg out) (evalOp : Eval Op)
    (input : Env Input) : BitVec arg.val :=
  evalOp g.seed (g.seedOperands.eval input)

def Diamond.resultValue (g : Diamond Op Input arg out) (evalOp : Eval Op)
    (input : Env Input) : BitVec out.val :=
  evalOp g.producer (.cons (g.seedValue evalOp input) .nil)

/-- Observe the actual entry transfer followed by the actual arm transfer. -/
def throughArm {hoisted : Bool} (cfg : Cfg Op (Label arg out hoisted) Input [out, out])
    (evalOp : Eval Op) (input : Env Input) : Frame (Label arg out hoisted) ⊕ Env [out, out] :=
  match cfg.entry.eval evalOp (fun term env => term.eval env) input with
  | .inl arm => (cfg.block arm.label).eval evalOp (fun term env => term.eval env)
      (arm.args.append input)
  | .inr result => .inr result

/-- The result and untouched arm payload supplied to the join. -/
def Diamond.joinArgs (g : Diamond Op Input arg out) (evalOp : Eval Op)
    (input : Env Input) : Env [out, out] :=
  if (input.get g.selector).getLsbD 0 then
    .cons (g.resultValue evalOp input) (.cons (input.get g.leftExtra) .nil)
  else
    .cons (input.get g.fallback) (.cons (input.get g.rightExtra) .nil)

end Silmaril.SSA.SeaOfNodes.GCM.Hoist

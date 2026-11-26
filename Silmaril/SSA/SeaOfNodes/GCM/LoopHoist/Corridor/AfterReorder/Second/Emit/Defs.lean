module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Defs

/-! # Apply the checked consumer move to the emitted one-save CFG -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Edge Frame Terminator)
open Silmaril.MLIR.SCF (For)
open Loop.MLIR.CF (Program TargetOp evalOp)

variable {Input Γ Δ extra : List Width} {saved consumer carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

abbrev TargetCfg (prepared : Prepared Input carried result) :=
  Cfg TargetOp (Label prepared.intermediate.1 carried result [prepared.consumer.width]) Input [result]

/-- Lift the existing packet by prepending the new saved result to a
header transfer. The prior saved result and latch retain their order. -/
abbrev carryConsumer (value : BitVec consumer.val) :
    Frame (Label saved carried result) → Frame (Label saved carried result [consumer]) :=
  Saved.prependFrame value

def liftEdge (rename : Rename Γ Δ) (keep : Var Δ consumer) :
    Edge (Label saved carried result extra) Γ → Edge (Label saved carried result (consumer :: extra)) Δ
  | ⟨.header, args⟩ => ⟨.header, .cons keep (For.renameOperands rename args)⟩
  | ⟨.exit, args⟩ => ⟨.exit, For.renameOperands rename args⟩

def liftTerm (rename : Rename Γ Δ) (keep : Var Δ consumer) :
    Terminator (Label saved carried result extra) [result] Γ →
      Terminator (Label saved carried result (consumer :: extra)) [result] Δ
  | .br edge => .br (liftEdge rename keep edge)
  | .condBr test onTrue onFalse => .condBr (rename test) (liftEdge rename keep onTrue) (liftEdge rename keep onFalse)
  | .ret values => .ret (For.renameOperands rename values)

def liftCode : {Γ Δ : List Width} → Rename Γ Δ → Var Δ consumer →
    Block TargetOp (Label saved carried result extra) Γ [result] →
    Block TargetOp (Label saved carried result (consumer :: extra)) Δ [result]
  | _, _, rename, keep, .terminator term => .terminator (liftTerm rename keep term)
  | _, _, rename, keep, .letOp op operands rest =>
    .letOp op (For.renameOperands rename operands) (liftCode (under rename) (.there keep) rest)

/-- Remove this binding in the current header and replace its uses with the
new parameter. Reindex the kept prefix and all successor arguments. -/
def rewriteAt? : Nat → {Γ Δ : List Width} → Rename Γ Δ → Var Δ consumer →
    Block TargetOp (Label saved carried result extra) Γ [result] →
    Option (Block TargetOp (Label saved carried result (consumer :: extra)) Δ [result])
  | 0, _, _, rename, keep, .letOp (w := width) _ _ rest =>
    if same : width = consumer then by
      subst width
      exact some (liftCode (replaceBinding rename keep) keep rest)
    else none
  | index + 1, _, _, rename, keep, .letOp op operands rest =>
    (rewriteAt? index (under rename) (.there keep) rest).map
      (.letOp op (For.renameOperands rename operands))
  | _, _, _, _, _, .terminator _ => none

/-- Apply the edit to a checked handoff. Insert immediately after the
leading save and remove the binding at the handoff's current header index.
The exit returns the same operand tuple. -/
def emit? (prepared : Prepared Input carried result) : Option (TargetCfg prepared) :=
  let cfg := prepared.intermediate.2
  match cfg.entry with
  | .letOp (w := width) producer operands tail =>
    if same : width = prepared.intermediate.1 then by
      subst width
      exact do
        let header ← rewriteAt? prepared.index Var.there .here (cfg.block .header)
        let .terminator (.ret returns) := cfg.block .exit | none
        pure
          { entry := .letOp producer operands
              (.letOp prepared.consumer.op prepared.consumer.inputs (liftCode Var.there .here tail))
            block
              | .header => header
              | .exit => .terminator (.ret returns) }
    else none
  | .terminator _ => none

structure Emission (Input : List Width) (carried result : Width) where
  prepared : Prepared Input carried result
  cfg : TargetCfg prepared

/-- Replay both nominations by original identity. A failed placement or
edit yields no emitted CFG. -/
def replay? (g : Program Input carried result entrySigs headerSigs) (first : AfterReorder.Plan)
    (consumerOrigin : Nat) : Option (Emission Input carried result) := do
  let prepared ← prepare? g first consumerOrigin
  let cfg ← emit? prepared
  pure ⟨prepared, cfg⟩

/-- Exact sequential transfers on the packets routed by the first hoist.
The same branch is taken. A header edge adds the new save in front of the
old packet, and every exit edge retains its entire payload. -/
abbrev StepRoutes
    (source : Cfg TargetOp (Label saved carried result) Input [result])
    (target : Cfg TargetOp (Label saved carried result [consumer]) Input [result])
    (input : Env Input) (first : BitVec saved.val) (second : BitVec consumer.val) : Prop :=
  Saved.StepRoutes source target input (.cons first .nil) second

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit

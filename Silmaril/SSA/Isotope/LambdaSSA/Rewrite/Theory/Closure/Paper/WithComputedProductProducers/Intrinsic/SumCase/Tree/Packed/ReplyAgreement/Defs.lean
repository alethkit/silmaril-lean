module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Defs

/-! # Selected trees for witnessed requests that return their bound payload -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement

open Silmaril
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
  (Bit Position ProgramBody signature Op)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The witnessed arm returns its actual bound bit, with its original finite
emit prefix and typed outward position. -/
abbrev DirectProgram (L : List (Ty Empty)) :=
  {p : ProgramBody L // p.left.result = .payload ∧ p.right.result = .payload}

/-- Execute the prefix in order while retaining the input to the final term. -/
def emitPrefix {X : Ty Empty} : List Bool → Term signature.Instr X Bit → Term signature.Instr X Bit
  | [], body => body
  | b :: bs, body =>
    .seq (.pair (.call (show signature.Instr from Op.emit b) .unit) (emitPrefix bs body)) (.snd unit Bit)

/-- Read the live payload after emitting the prefix and take the recorded exit. -/
def payloadLeaf {L : List (Ty Empty)} (emits : List Bool) (position : Position L) :
    CaseTree signature.Instr (product unit Bit) L :=
  .exit position.1 position.typed (.returned (emitPrefix emits (.snd unit Bit)))

/-- Select the source request and both witnessed arms at their original
ordered interface. The intrinsic input is the unit coordinate of the closed
LetCase environment. -/
def DirectProgram.selected {L : List (Ty Empty)} (p : DirectProgram L) :
    CaseTree signature.Instr unit L :=
  .case Bit Bit (.call (show signature.Instr from Op.ask p.val.request) .unit)
    (payloadLeaf p.val.left.emits p.val.left.position)
    (payloadLeaf p.val.right.emits p.val.right.position)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement

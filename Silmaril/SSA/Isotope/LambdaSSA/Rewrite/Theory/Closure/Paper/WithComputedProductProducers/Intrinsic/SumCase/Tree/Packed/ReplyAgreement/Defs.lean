module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Defs

/-! # Selected trees for witnessed requests that return their bound payload -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement

open Silmaril
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The witnessed arm returns its actual bound bit, with its original finite
emit prefix and typed outward position. -/
abbrev DirectProgram (L : List (Ty Empty)) :=
  {p : ProgramBody L // p.left.result = .payload ∧ p.right.result = .payload}

/-- Execute the prefix in order while retaining the input to the final term. -/
def emitPrefix {X D : Ty Empty} : List Bool → Term signature.Instr X D → Term signature.Instr X D
  | [], body => body
  | b :: bs, body =>
    .seq (.pair (.call (show signature.Instr from Op.emit b) .unit) (emitPrefix bs body)) (.snd unit D)

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

/-- The selected context stores older replies on the left and the newest on the right. -/
def replyContext : Nat → Ty Empty
  | 0 => unit
  | n + 1 => product (replyContext n) Bit

/-- A witnessed slot is newest-first. Follow the left fields to read an older reply. -/
def readReply : (n : Nat) → Fin n → Term signature.Instr (replyContext n) Bit
  | 0, i => i.elim0
  | n + 1, i =>
    Fin.cases (.snd (replyContext n) Bit)
      (fun older => .seq (.fst (replyContext n) Bit) (readReply n older)) i

/-- The shared finite fragment groups emits before each request or return.
A leaf reads a retained reply at a typed ordered exit. -/
inductive ReadTree (L : List (Ty Empty)) : Nat → Type where
  | ret {n : Nat} (emits : List Bool) (position : Position L) (index : Fin n) : ReadTree L n
  | request {n : Nat} (emits : List Bool) (label bound : Bool)
      (left right : ReadTree L (n + 1)) : ReadTree L n

/-- The actual source tree in the finite witnessed LetCase grammar. -/
def ReadTree.witnessed {L : List (Ty Empty)} {n : Nat} : ReadTree L n → Finite.Tree L n
  | .ret emits position index => emits.foldr Finite.Tree.emit (.ret position (.read index))
  | .request emits label bound left right =>
    emits.foldr Finite.Tree.emit (.request label bound left.witnessed right.witnessed)

/-- Compile arbitrarily many finite requests using the packed context at each arm. -/
def ReadTree.selected {L : List (Ty Empty)} {n : Nat} :
    ReadTree L n → CaseTree signature.Instr (replyContext n) L
  | .ret emits position index =>
    .exit position.1 position.typed (.returned (emitPrefix emits (readReply n index)))
  | .request emits label _ left right =>
    .case Bit Bit (emitPrefix emits (.call (show signature.Instr from Op.ask label) .unit))
      left.selected right.selected

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement

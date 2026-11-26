module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Defs

/-! # Selected trees for witnessed requests and terminal reply expressions -/

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

/-- The native left and right injections encode the two literal bits. -/
def bitTag : Bool → ExitTag (unit : Ty Empty) Bit
  | false => .inl unit unit
  | true => .inr unit unit

/-- Compile a witnessed terminal expression. Its pure cases select only
terminal subexpressions. The initial emits run before the first test or return. -/
def selectTerminal {L : List (Ty Empty)} (position : Position L) :
    {n : Nat} → Finite.Expr n → {X : Ty Empty} →
      (Fin n → Term signature.Instr X Bit) → List Bool → CaseTree signature.Instr X L
  | _, .literal b, _, _, emits =>
    .taggedExit position.1 position.typed (bitTag b) (emitPrefix emits .unit)
  | _, .read i, _, slots, emits =>
    .exit position.1 position.typed (.returned (emitPrefix emits (slots i)))
  | _, .split low high, X, slots, emits =>
    let older := fun i => Term.seq (.fst X unit) (slots i.succ)
    .case unit unit (emitPrefix emits (slots 0))
      (selectTerminal position low older []) (selectTerminal position high older [])

/-- The shared finite fragment groups emits before each request or return.
A leaf returns a witnessed expression over retained replies at a typed ordered exit. -/
inductive ReadTree (L : List (Ty Empty)) : Nat → Type where
  | ret {n : Nat} (emits : List Bool) (position : Position L) (index : Fin n) : ReadTree L n
  | retExpr {n : Nat} (emits : List Bool) (position : Position L) (result : Finite.Expr n) : ReadTree L n
  | request {n : Nat} (emits : List Bool) (label bound : Bool)
      (left right : ReadTree L (n + 1)) : ReadTree L n

/-- The actual source tree in the finite witnessed LetCase grammar. -/
def ReadTree.witnessed {L : List (Ty Empty)} {n : Nat} : ReadTree L n → Finite.Tree L n
  | .ret emits position index => emits.foldr Finite.Tree.emit (.ret position (.read index))
  | .retExpr emits position result => emits.foldr Finite.Tree.emit (.ret position result)
  | .request emits label bound left right =>
    emits.foldr Finite.Tree.emit (.request label bound left.witnessed right.witnessed)

/-- Compile arbitrarily many finite requests using the packed context at each arm. -/
def ReadTree.selected {L : List (Ty Empty)} {n : Nat} :
    ReadTree L n → CaseTree signature.Instr (replyContext n) L
  | .ret emits position index =>
    .exit position.1 position.typed (.returned (emitPrefix emits (readReply n index)))
  | .retExpr emits position result => selectTerminal position result (readReply n) emits
  | .request emits label _ left right =>
    .case Bit Bit (emitPrefix emits (.call (show signature.Instr from Op.ask label) .unit))
      left.selected right.selected

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement

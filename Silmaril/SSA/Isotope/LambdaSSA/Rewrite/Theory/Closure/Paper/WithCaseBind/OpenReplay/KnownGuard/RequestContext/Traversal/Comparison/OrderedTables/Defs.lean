module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Compact.Thms

/-! # Canonical ordered truth tables for selected programs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.OrderedTables

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Each terminal gets the full quote of one Boolean table, including
constant and projection results. The existing normal form records effects,
reply choices, and ordered typed exits. -/
def renderWith {L : List (Ty Empty)} : {n : Nat} → Finite.Normal L n → List Bool → ReadTree L n
  | n, .ret pos table, emits => .retExpr emits pos (Finite.Expr.quote n table)
  | _, .emit bit next, emits => renderWith next (emits ++ [bit])
  | _, .request label l r, emits => .request emits label false (renderWith l []) (renderWith r [])
  | _, .testRequest test low fl fr tl tr, emits =>
    .testRequest emits test low false false
      (renderWith fl []) (renderWith fr []) (renderWith tl []) (renderWith tr [])

def target {L : List (Ty Empty)} {n : Nat} (p : Finite.Normal L n) : ScopedTarget (replyContext n) L :=
  (renderWith p []).selected.elaborate

/-- Locate the very same typed projection in the retained order. -/
def locate {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin n → ReplyFrame.Slot frame) (slot : ReplyFrame.Slot frame) : Option (Fin n) :=
  letI := ReplyFrame.Slot.decEq frame
  (List.finRange n).find? fun j => decide (slots j = slot)

/-- Evaluate the original syntax in the canonical coordinates. Aliased
source slots resolve to the same coordinate. An unavailable projection
prevents admission if a read or a test with different arms needs it. -/
def reindex? {X : Ty Empty} {frame : ReplyFrame X} {n : Nat} (kept : Fin n → ReplyFrame.Slot frame) :
    {m : Nat} → Finite.Expr m → (Fin m → ReplyFrame.Slot frame) → Option (Finite.Table n)
  | _, .literal bit, _ => some (fun _ => bit)
  | _, .read i, slots => (locate kept (slots i)).map fun j env => env j
  | _, .split low high, slots =>
    let older := fun i => slots i.succ
    if low = high then reindex? kept low older else do
      let test ← locate kept (slots 0)
      let l ← reindex? kept low older
      let r ← reindex? kept high older
      pure fun env => if env test then r env else l env

/-- Follow the exact effect skeleton in canonical reply order. Guards have
complementary request labels and delete their tested slot on both sides. -/
def recoverTree {L : List (Ty Empty)} :
    {m : Nat} → ReadTree L m → {X : Ty Empty} → {frame : ReplyFrame X} →
    (Fin m → ReplyFrame.Slot frame) → {n : Nat} → (Fin n → ReplyFrame.Slot frame) → Option (Finite.Normal L n)
  | _, .ret emits pos i, _, _, slots, _, kept => do
    let j ← locate kept (slots i)
    pure (emits.foldr Finite.Normal.emit (.ret pos (fun env => env j)))
  | _, .retExpr emits pos e, _, _, slots, _, kept => do
    let table ← reindex? kept e slots
    pure (emits.foldr Finite.Normal.emit (.ret pos table))
  | _, .request emits label _ l r, _, _, slots, _, kept => do
    let l ← recoverTree l (ReplyFrame.bindSlots slots) (ReplyFrame.bindSlots kept)
    let r ← recoverTree r (ReplyFrame.bindSlots slots) (ReplyFrame.bindSlots kept)
    pure (emits.foldr Finite.Normal.emit (.request label l r))
  | _, .testRequest emits test low _ _ fl fr tl tr, _, _, slots, _ + 1, kept => do
    let i ← locate kept (slots test)
    let children := ReplyFrame.guardSlots slots test
    let retained := ReplyFrame.guardSlots kept i
    let fl ← recoverTree fl children retained
    let fr ← recoverTree fr children retained
    let tl ← recoverTree tl children retained
    let tr ← recoverTree tr children retained
    pure (emits.foldr Finite.Normal.emit (.testRequest i low fl fr tl tr))
  | _, .testRequest .., _, _, _, 0, _ => none

/-- Compare the original selected split with the canonical guard shell.
Both branches begin with their literal complementary requests. -/
def recoverSplit {L : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X} {m n : Nat}
    (p : SelectedGuardSplit L m) (slots : Fin m → ReplyFrame.Slot frame)
    (kept : Fin (n + 1) → ReplyFrame.Slot frame) : Option (Finite.Normal L (n + 1)) := do
  let i ← locate kept (slots p.test)
  match p.onFalse, p.onTrue with
  | .request [] low _ fl fr, .request [] high _ tl tr =>
    if high = !low then do
      let children := ReplyFrame.bindSlots (fun j => ReplyFrame.Slot.retainUnit (slots j))
      let retained := ReplyFrame.guardSlots kept i
      let fl ← recoverTree fl children retained
      let fr ← recoverTree fr children retained
      let tl ← recoverTree tl children retained
      let tr ← recoverTree tr children retained
      pure (p.emits.foldr Finite.Normal.emit (.testRequest i low fl fr tl tr))
    else none
  | _, _ => none

/-- A canonical key with a native certificate for the actual original arrow. -/
structure Admission {L : List (Ty Empty)} {n : Nat} (p : SelectedAt (replyContext n) L) where
  key : Finite.Normal L n
  packed_eq : p.packedSource = (target key).packed

/-- On admitted programs the result either proves native equality or
returns a distinguishing input in the validated payload trace model. -/
inductive Decision {L : List (Ty Empty)} {n : Nat} (p q : SelectedAt (replyContext n) L) where
  | equal (proof : p.packedSource = q.packedSource)
  | different (input : Finite.Assignment n)
      (proof : CanonicalLive.observations p input ≠ CanonicalLive.observations q input)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.OrderedTables

module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Defs

/-! # Schedule the effects in a written request operand -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed

open LambdaSSA (FiniteCFG Flat Region Tm)
open Morphism.CaseSSA (erase)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Expr PacketType PrimitiveSignature Slot elaborateExpr)

variable {F : Type} {blocks exits captures : Nat} {Γ Δ Θ : List PacketType}
  {sig : PrimitiveSignature F} {ty : PacketType}

/-- The checked operand grammar shares structural leaves with the public
dispatcher. A primitive's argument is checked recursively at its input type. -/
inductive Operand (sig : PrimitiveSignature F) (Γ : List PacketType) : PacketType → Type
  | pure {a : PacketType} (value : Expr Γ a) : Operand sig Γ a
  | pair {a b : PacketType} (left : Operand sig Γ a) (right : Operand sig Γ b) :
      Operand sig Γ (.product a b)
  | call (op : F) (arg : Operand sig Γ (sig.argument op)) : Operand sig Γ (sig.reply op)

def Operand.written : {ty : PacketType} → Operand sig Γ ty → Tm F
  | _, .pure value => operand position value
  | _, .pair left right => .pair left.written right.written
  | _, .call op arg => .op op arg.written

abbrev SlotMap (Γ Δ : List PacketType) := ∀ {a}, Slot Γ a → Slot Δ a

def renameExpr (slots : SlotMap Γ Δ) : {ty : PacketType} → Expr Γ ty → Expr Δ ty
  | _, .var slot => .var (slots slot)
  | _, .unit => .unit
  | _, .pair left right => .pair (renameExpr slots left) (renameExpr slots right)

/-- Each scheduled application has a structural argument and adds its
typed reply to the current scope. -/
inductive Requests (sig : PrimitiveSignature F) : List PacketType → List PacketType → Type
  | done {Γ : List PacketType} : Requests sig Γ Γ
  | request {Γ Δ : List PacketType} (op : F) (arg : Expr Γ (sig.argument op))
      (next : Requests sig (sig.reply op :: Γ) Δ) : Requests sig Γ Δ

def Requests.append : {Γ Δ : List PacketType} → Requests sig Γ Δ → Requests sig Δ Θ → Requests sig Γ Θ
  | _, _, .done, next => next
  | _, _, .request op arg rest, next => .request op arg (rest.append next)

/-- Embed an older typed slot through every reply binder. -/
def Requests.slots : {Γ Δ : List PacketType} → Requests sig Γ Δ → SlotMap Γ Δ
  | _, _, .done, _, slot => slot
  | _, _, .request _ _ next, _, slot => next.slots (.there slot)

/-- The same embedding for raw lexical indices, including the caller's
ambient environment beyond the checked slots. -/
def Requests.shift : {Γ Δ : List PacketType} → Requests sig Γ Δ → Nat → Nat
  | _, _, .done, i => i
  | _, _, .request _ _ next, i => next.shift (i + 1)

/-- Insert the scheduled requests as ordinary written lets. -/
def Requests.wrap {A : Type} (bind : Tm F → A → A) :
    {Γ Δ : List PacketType} → Requests sig Γ Δ → A → A
  | _, _, .done, body => body
  | _, _, .request op arg next, body => bind (.op op (operand position arg)) (next.wrap bind body)

structure Scheduled (sig : PrimitiveSignature F) (Γ : List PacketType) (ty : PacketType) where
  scope : List PacketType
  requests : Requests sig Γ scope
  value : Expr scope ty

/-- Schedule a product left to right. The right operand uses the original
slots behind the left replies. The final pair retains the left result
behind the right replies. -/
def Operand.scheduleAt : {ty : PacketType} → Operand sig Γ ty →
    {Δ : List PacketType} → SlotMap Γ Δ → Scheduled sig Δ ty
  | _, .pure value, Δ, slots => ⟨Δ, .done, renameExpr slots value⟩
  | _, .pair left right, _, slots =>
    let l := left.scheduleAt slots
    let r := right.scheduleAt (fun slot => l.requests.slots (slots slot))
    ⟨r.scope, l.requests.append r.requests, .pair (renameExpr r.requests.slots l.value) r.value⟩
  | _, .call op arg, _, slots =>
    let result := arg.scheduleAt slots
    ⟨sig.reply op :: result.scope, result.requests.append (.request op result.value .done), .var .here⟩

def Operand.schedule (arg : Operand sig Γ ty) : Scheduled sig Γ ty :=
  arg.scheduleAt (fun slot => slot)

def Scheduled.term (scheduled : Scheduled sig Γ ty) : Tm F :=
  scheduled.requests.wrap Tm.let₁ (operand position scheduled.value)

def readOperand (sig : PrimitiveSignature F) (Γ : List PacketType) :
    Tm F → Option (Σ ty : PacketType, Operand sig Γ ty)
  | .op op arg => do
    let ⟨ty, arg⟩ ← readOperand sig Γ arg
    if typed : ty = sig.argument op then
      some ⟨sig.reply op, .call op (typed ▸ arg)⟩
    else none
  | .pair left right => do
    let ⟨a, left⟩ ← readOperand sig Γ left
    let ⟨b, right⟩ ← readOperand sig Γ right
    return ⟨.product a b, .pair left right⟩
  | raw => do
    let ⟨ty, value⟩ ← elaborateExpr Γ raw
    return ⟨ty, .pure value⟩

/-- Insert all scheduled replies below the outer request's binder.
Its own reply keeps slot zero. -/
def hoist (outer : F) (arg : Operand sig Γ (sig.argument outer)) (tail : Region F) : Region F :=
  let scheduled := arg.schedule
  scheduled.requests.wrap Region.let₁
    (.let₁ (.op outer (operand position scheduled.value))
      (tail.renameVars (Silmaril.DeBruijn.lift scheduled.requests.shift)))

structure Lifted (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (source : FiniteCFG F blocks exits captures) where
  outer : F
  argument : Operand sig context.toList (sig.argument outer)
  tail : Flat F (blocks + exits) (captures + 1)
  source_eq : source.entry.erase = .let₁ (.op outer argument.written) tail.erase
  entry : Flat F (blocks + exits) captures
  entry_eq : entry.erase = hoist outer argument tail.erase

def Lifted.code {context : BoundCtx PacketType captures} {source : FiniteCFG F blocks exits captures}
    (lifted : Lifted sig context source) : FiniteCFG F blocks exits captures :=
  ⟨lifted.entry, source.block⟩

/-- Check the first written request's operand. Require its exact erased
syntax and outer argument type before reifying the hoisted entry. -/
def lift [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (source : FiniteCFG F blocks exits captures) : Option (Lifted sig context source) :=
  match h : source.entry with
  | .let₁ (.op outer original) tail => do
    let ⟨ty, arg⟩ ← readOperand sig context.toList (erase original)
    if typed : ty = sig.argument outer then
      let arg := typed ▸ arg
      if exactArg : erase original = arg.written then
        let entry ← scopedRow (blocks + exits) captures (hoist outer arg tail.erase)
        return ⟨outer, arg, tail, by
          rw [h]
          change Region.let₁ (.op outer (erase original)) tail.erase = _
          rw [exactArg], entry.val, entry.property⟩
      else none
    else none
  | _ => none

structure Compiled (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  lifted : Lifted sig context source
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  checked : Multiple.Compiled sig context packets outputs lifted.code

/-- Check the original CFG and lower its operand schedule through the
existing recursive continuation compiler. The old block table is shared. -/
def compile [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Compiled sig context packets outputs source) :=
  letI := sig.typing;
  if original : NamedFlat.check source context packets outputs = true then
    match lift sig context source with
    | none => none
    | some lifted =>
      (Multiple.compile sig context packets outputs lifted.code).map fun checked =>
        ⟨lifted, NamedFlat.check_sound _ _ _ _ original, checked⟩
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed

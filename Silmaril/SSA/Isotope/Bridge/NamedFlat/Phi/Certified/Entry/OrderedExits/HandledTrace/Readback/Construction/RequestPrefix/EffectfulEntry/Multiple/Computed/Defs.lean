module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Defs

/-! # Check one nested effect in a written request operand -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed

open LambdaSSA (FiniteCFG Flat Region Tm)
open Morphism.CaseSSA (erase)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Expr PacketType PrimitiveSignature elaborateArg elaborateExpr)

variable {F : Type} {blocks exits captures : Nat} {Γ : List PacketType}
  {sig : PrimitiveSignature F} {op : F} {ty : PacketType}

/-- One primitive application, optionally nested in product fields.
Its argument and all sibling expressions are structural. -/
inductive Operand (sig : PrimitiveSignature F) (Γ : List PacketType) : F → PacketType → Type
  | call (op : F) (arg : Expr Γ (sig.argument op)) : Operand sig Γ op (sig.reply op)
  | left {op : F} {a b : PacketType} (left : Operand sig Γ op a) (right : Expr Γ b) : Operand sig Γ op (.product a b)
  | right {op : F} {a b : PacketType} (left : Expr Γ a) (right : Operand sig Γ op b) : Operand sig Γ op (.product a b)

def Operand.argument : {ty : PacketType} → Operand sig Γ op ty → Expr Γ (sig.argument op)
  | _, .call _ arg => arg
  | _, .left effect _ => effect.argument
  | _, .right _ effect => effect.argument

def Operand.written : {op : F} → {ty : PacketType} → Operand sig Γ op ty → Tm F
  | _, _, .call opcode arg => .op opcode (operand position arg)
  | _, _, .left effect sibling => .pair effect.written (operand position sibling)
  | _, _, .right sibling effect => .pair (operand position sibling) effect.written

def weaken {added : PacketType} : {ty : PacketType} → Expr Γ ty → Expr (added :: Γ) ty
  | _, .var slot => .var (.there slot)
  | _, .unit => .unit
  | _, .pair left right => .pair (weaken left) (weaken right)

/-- In the extended scope, the result of the one request is slot zero. -/
def Operand.residual : {ty : PacketType} → Operand sig Γ op ty → Expr (sig.reply op :: Γ) ty
  | _, .call _ _ => .var .here
  | _, .left effect sibling => .pair effect.residual (weaken sibling)
  | _, .right sibling effect => .pair (weaken sibling) effect.residual

def readOperand (sig : PrimitiveSignature F) (Γ : List PacketType) :
    Tm F → Option (Σ op : F, Σ ty : PacketType, Operand sig Γ op ty)
  | .op op arg => do
    let arg ← elaborateArg Γ (sig.argument op) arg
    return ⟨op, sig.reply op, .call op arg⟩
  | .pair left right =>
    match readOperand sig Γ left with
    | some ⟨op, a, effect⟩ => do
      let ⟨b, pureRight⟩ ← elaborateExpr Γ right
      return ⟨op, .product a b, .left effect pureRight⟩
    | none => do
      let ⟨a, pureLeft⟩ ← elaborateExpr Γ left
      let ⟨op, b, effect⟩ ← readOperand sig Γ right
      return ⟨op, .product a b, .right pureLeft effect⟩
  | _ => none

/-- Insert the inner reply below the outer request's binder. The outer
reply keeps slot zero and the original captures shift by one. -/
def hoist (outer : F) (arg : Operand sig Γ op (sig.argument outer)) (tail : Region F) : Region F :=
  .let₁ (.op op (operand position arg.argument))
    (.let₁ (.op outer (operand position arg.residual)) (tail.renameVars (Silmaril.DeBruijn.lift Nat.succ)))

structure Lifted (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (source : FiniteCFG F blocks exits captures) where
  outer : F
  inner : F
  argument : Operand sig context.toList inner (sig.argument outer)
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
    let ⟨inner, ty, arg⟩ ← readOperand sig context.toList (erase original)
    if typed : ty = sig.argument outer then
      let arg := typed ▸ arg
      if exactArg : erase original = arg.written then
        let entry ← scopedRow (blocks + exits) captures (hoist outer arg tail.erase)
        return ⟨outer, inner, arg, tail, by
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

/-- Check the original CFG and lift one operand effect into the existing
recursive continuation compiler. Old blocks remain the original blocks. -/
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

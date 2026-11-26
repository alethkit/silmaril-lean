module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Defs

/-! # Compact terminals over a shared finite request skeleton -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance compactReplayDefsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- A compact terminal and the permutation selecting its logical slots from the physical reply packet. -/
structure OrderedExpr (n : Nat) where
  expr : Finite.Expr n
  order : Equiv.Perm (Fin n)

/-- Evaluate the terminal in physical packet coordinates. -/
def OrderedExpr.packetEval {n : Nat} (e : OrderedExpr n) : Finite.Table n :=
  fun row => e.expr.eval (row ∘ e.order)

/-- Compare the right terminal at the same packet, expressed in the left terminal’s logical coordinates. -/
def OrderedExpr.Agrees {n : Nat} (e f : OrderedExpr n) : Prop :=
  ∀ row, e.expr.eval row = f.expr.eval ((row ∘ e.order.symm) ∘ f.order)

/-- Compile the compact expression with its actual ordered slot map. -/
def OrderedExpr.selected {n : Nat} {L : List (Ty Empty)} (e : OrderedExpr n)
    (emits : List Bool) (pos : Position L) : CaseTree signature.Instr (replyContext n) L :=
  selectTerminal pos e.expr (readReply n ∘ e.order) emits

/-- A shared tree of effectful requests and terminal emits. Each terminal fixes its typed outward position. -/
inductive RequestSkeleton (L : List (Ty Empty)) : Nat → Type where
  | ret {n : Nat} (emits : List Bool) (pos : Position L) : RequestSkeleton L n
  | request {n : Nat} (emits : List Bool) (label : Bool)
      (left right : RequestSkeleton L (n + 1)) : RequestSkeleton L n

/-- Supply a compact expression and independent slot order at each terminal. -/
def RequestSkeleton.Leaves {L : List (Ty Empty)} : {n : Nat} → RequestSkeleton L n → Type
  | n, .ret _ _ => OrderedExpr n
  | _, .request _ _ left right => left.Leaves × right.Leaves

/-- Compile the compact terminals at the packet reached by their request path. -/
def RequestSkeleton.selected {L : List (Ty Empty)} : {n : Nat} → (s : RequestSkeleton L n) →
    s.Leaves → CaseTree signature.Instr (replyContext n) L
  | _, .ret emits pos, e => e.selected emits pos
  | _, .request emits label left right, leaves =>
    selectRequest emits label (left.selected leaves.1) (right.selected leaves.2)

/-- A standard-order witnessed tree of the same request shape, with its terminal tables in physical coordinates. -/
def RequestSkeleton.quoted {L : List (Ty Empty)} : {n : Nat} → (s : RequestSkeleton L n) →
    s.Leaves → ReadTree L n
  | n, .ret emits pos, e => .retExpr emits pos (Finite.Expr.quote n e.packetEval)
  | _, .request emits label left right, leaves =>
    .request emits label false (left.quoted leaves.1) (right.quoted leaves.2)

/-- Require extensional agreement separately at each terminal of the common skeleton. -/
def RequestSkeleton.Agrees {L : List (Ty Empty)} : {n : Nat} → (s : RequestSkeleton L n) →
    s.Leaves → s.Leaves → Prop
  | _, .ret _ _, e, f => e.Agrees f
  | _, .request _ _ left right, l, r => left.Agrees l.1 r.1 ∧ right.Agrees l.2 r.2

/-- Pack the actual compact elaboration at the original input and exit interface. -/
def RequestSkeleton.packed {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (leaves : s.Leaves) :
    Paper.Extension.Singleton.ofType Seed (replyContext n) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed (s.selected leaves).elaborate.property.packExits

/-- Admission for the existing selected trees whose internal nodes are ordinary requests. -/
inductive RequestOnly {L : List (Ty Empty)} : {n : Nat} → ReadTree L n → Type where
  | ret {n : Nat} (emits : List Bool) (pos : Position L) (i : Fin n) :
      RequestOnly (.ret emits pos i)
  | retExpr {n : Nat} (emits : List Bool) (pos : Position L) (e : Finite.Expr n) :
      RequestOnly (.retExpr emits pos e)
  | request {n : Nat} {l r : ReadTree L (n + 1)} (emits : List Bool) (label bound : Bool)
      (hl : RequestOnly l) (hr : RequestOnly r) : RequestOnly (.request emits label bound l r)

/-- A presentation of the actual selected tree by the shared request grammar. -/
structure RequestPresentation {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n) where
  skeleton : RequestSkeleton L n
  leaves : skeleton.Leaves
  selected_eq : skeleton.selected leaves = p.selected

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

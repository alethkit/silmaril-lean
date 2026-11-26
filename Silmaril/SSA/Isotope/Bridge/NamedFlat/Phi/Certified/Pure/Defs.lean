module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Defs

/-! # Pure projections for the certified φ capture record -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Flat Region)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive)
open LetCase.LocallyNameless (Tm)

universe u v w x
variable {F : Type v} {Base : Type u} {n : Nat}

/-- Extend the target signature with a typed read of each initial capture slot.
A closed packet expression can use these reads without a caller's opcode. -/
inductive Instruction (F : Type v) (β : BoundCtx (Ty Base) n) where
  | original (f : F)
  | slot (i : Fin n)

variable {β : BoundCtx (Ty Base) n}

instance [HasTy F (Ty Base)] : HasTy (Instruction F β) (Ty Base) where
  src
    | .original f => instrSrc f
    | .slot _ => .unit
  trg
    | .original f => instrTrg f
    | .slot i => β.get i

/-- Embed existing instructions without changing the variables or binders. -/
def embedTerm : {m : Nat} → Tm Empty F m → Tm Empty (Instruction F β) m
  | _, .fv x => x.elim
  | _, .bv i => .bv i
  | _, .op f a => .op (.original f) (embedTerm a)
  | _, .let₁ a b => .let₁ (embedTerm a) (embedTerm b)
  | _, .unit => .unit
  | _, .pair a b => .pair (embedTerm a) (embedTerm b)
  | _, .let₂ a b => .let₂ (embedTerm a) (embedTerm b)
  | _, .inl a => .inl (embedTerm a)
  | _, .inr a => .inr (embedTerm a)
  | _, .case a l r => .case (embedTerm a) (embedTerm l) (embedTerm r)
  | _, .abort a => .abort (embedTerm a)

def embedFlat {labels : Nat} : {m : Nat} → Flat F labels m → Flat (Instruction F β) labels m
  | _, .br i a => .br i (embedTerm a)
  | _, .let₁ a b => .let₁ (embedTerm a) (embedFlat b)
  | _, .let₂ a b => .let₂ (embedTerm a) (embedFlat b)
  | _, .case a l r => .case (embedTerm a) (embedFlat l) (embedFlat r)

/-- Embed only original operations in the admitted table. Slot reads first
appear in the closure entry. -/
def embed {blocks exits m : Nat} (graph : FiniteCFG F blocks exits m) :
    FiniteCFG (Instruction F β) blocks exits m :=
  ⟨embedFlat graph.entry, fun i => embedFlat (graph.block i)⟩

/-- Assemble a closed record in the order of `Region.packedInputType` and
`Capture.packEnv`, with newest slot at the right. -/
def assemble {G : Type v} : (m : Nat) → (Fin m → Tm Empty G 0) → Tm Empty G 0
  | 0, _ => .unit
  | m + 1, slots => .pair (assemble m (slots ∘ Fin.succ)) (slots 0)

/-- Synthesize the packet producer from the admitted capture profile. -/
def packetInput (F : Type v) (β : BoundCtx (Ty Base) n) : Tm Empty (Instruction F β) 0 :=
  assemble n (fun i => .op (.slot i) .unit)

/-- Preserve original primitive trees and read the initial slots without
emitting any visible event. The slot operations generated here receive unit. -/
def treePrimitives {Events : Type w → Type w} {α : Type x} (instr : Primitive Events F α)
    (slots : Env α) : Primitive Events (Instruction F β) α
  | .original f => instr f
  | .slot i => fun _ => pure (slots i.val)

/-- Preserve the original partial primitives and return each initial slot. -/
def partPrimitives {α : Type u} (prim : F → Value α → Part (Value α))
    (slots : Env α) : Instruction F β → Value α → Part (Value α)
  | .original f => prim f
  | .slot i => fun _ => Part.some (slots i.val)

variable {V K : Type u} [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
  {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
  {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}

/-- A checked target linked to the original admission and the generated
packet expression. Its entry alone uses the added slot reads. -/
structure Closed (admitted : Admission source inputs captures β R L) where
  graph : FiniteCFG (Instruction F β) (blockCount source) 1 0
  typed : graph.HasType .nil R L
  closes : Capture.Closes β (packetInput F β) (embed admitted.graph) graph

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture

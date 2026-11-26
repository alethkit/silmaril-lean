module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Defs

/-! # Outline independent requests in a written entry tree -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple

open LambdaSSA (FiniteCFG Region)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Expr PacketType PrimitiveSignature elaborateBranch elaborateExpr)

variable {F : Type} {blocks exits captures n newBlocks : Nat} {Γ : List PacketType}
  {sig : PrimitiveSignature F} {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}

/-- A checked entry tree indexed by the number of appended rows.
A request leaf owns two consecutive rows. Each case divides its suffix
into disjoint left and right intervals. -/
inductive EntryTree (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) : List PacketType → Nat → Type
  | pure {Γ : List PacketType} (tail : CaseTail packets outputs Γ) : EntryTree sig packets outputs Γ 0
  | request {Γ : List PacketType} (leaf : Request sig packets outputs Γ) : EntryTree sig packets outputs Γ 2
  | case {Γ : List PacketType} {a b : PacketType} {l r : Nat} (test : Expr Γ (.coprod a b))
      (left : EntryTree sig packets outputs (a :: Γ) l) (right : EntryTree sig packets outputs (b :: Γ) r) :
      EntryTree sig packets outputs Γ (l + r)

def EntryTree.written : {Γ : List PacketType} → {n : Nat} → EntryTree sig packets outputs Γ n → Region F
  | _, _, .pure tail => CaseTail.erase id position tail
  | _, _, .request leaf => leaf.row.erase
  | _, _, .case test left right => .case (operand position test) left.written right.written

def EntryTree.entry (old : Fin blocks → Fin newBlocks) :
    {Γ : List PacketType} → {n : Nat} → EntryTree sig packets outputs Γ n → (Fin n → Fin newBlocks) → Region F
  | _, _, .pure tail, _ => CaseTail.erase old position tail
  | _, _, .request leaf, labels => leaf.jumpAt (labels 0)
  | _, _, .case (r := r) test left right, labels =>
    .case (operand position test) (left.entry old (fun i => labels (i.castAdd r)))
      (right.entry old (fun i => labels (i.natAdd _)))

def EntryTree.cells (old : Fin blocks → Fin newBlocks) :
    {Γ : List PacketType} → {n : Nat} → EntryTree sig packets outputs Γ n →
      (Fin n → Fin newBlocks) → Fin n → PacketType × Region F
  | _, _, .pure _, _ => Fin.elim0
  | _, _, .request leaf, labels => leaf.cellsAt old labels
  | _, _, .case (r := r) _ left right, labels =>
    appendTable (left.cells old (fun i => labels (i.castAdd r))) (right.cells old (fun i => labels (i.natAdd _)))

/-- Recursively check structural case tests and their typed binder scopes.
Each request delegates to the same one-request checker as the selected
path API. A second request in its continuation is rejected there. -/
def read (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType) :
    (Γ : List PacketType) → Region F → Option (Σ n, EntryTree sig packets outputs Γ n)
  | Γ, .case test left right => do
    let ⟨.coprod a b, discr⟩ ← elaborateExpr Γ test | none
    let ⟨_, left⟩ ← read sig packets outputs (a :: Γ) left
    let ⟨_, right⟩ ← read sig packets outputs (b :: Γ) right
    return ⟨_, .case discr left right⟩
  | Γ, .let₁ arg tail => do
    let leaf ← readRequest sig packets outputs Γ (.let₁ arg tail)
    return ⟨2, .request leaf⟩
  | Γ, .br label arg => do
    let tail ← elaborateBranch (Sum.elim packets outputs) Γ (.br label arg)
    return ⟨0, .pure tail⟩
  | _, _ => none

def EntryTree.profile (tree : EntryTree sig packets outputs Γ n) : Fin (blocks + n) → PacketType :=
  appendTable packets fun i => (tree.cells (oldLabel n) (freshLabel blocks) i).1

structure Outlined (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  count : Nat
  tree : EntryTree sig packets outputs context.toList count
  emitted : Assembly source tree.written (tree.entry (oldLabel count) (freshLabel blocks))
    (tree.cells (oldLabel count) (freshLabel blocks))

def outline [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Outlined sig context packets outputs source) := do
  let ⟨count, tree⟩ ← read sig packets outputs context.toList source.entry.erase
  let emitted ← assemble source tree.written (tree.entry (oldLabel count) (freshLabel blocks))
    (tree.cells (oldLabel count) (freshLabel blocks))
  return ⟨count, tree, emitted⟩

structure Compiled (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  outlined : Outlined sig context packets outputs source
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  prepared : BranchEntry.Prepared sig context outlined.tree.profile outputs outlined.emitted.code
  publicReadback : Constructed sig (BranchEntry.profile context outlined.tree.profile)
    outputs prepared.emitted.code

/-- Use the ordinary structural entry adapter and exact public row
checker on the table with all request leaves outlined. -/
def compile [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Compiled sig context packets outputs source) :=
  letI := sig.typing;
  if original : NamedFlat.check source context packets outputs = true then
    match outline sig context packets outputs source with
    | none => none
    | some outlined =>
      match BranchEntry.prepare sig context outlined.tree.profile outputs outlined.emitted.code with
      | none => none
      | some prepared =>
        (construct sig (BranchEntry.profile context outlined.tree.profile) outputs prepared.emitted.code).map
          fun result => ⟨outlined, NamedFlat.check_sound _ _ _ _ original, prepared, result⟩
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple

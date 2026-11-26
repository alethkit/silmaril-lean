module

public import Mathlib.Algebra.BigOperators.Fin
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Defs

/-! # Schedule computed transfers across one original block table -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph

open LambdaSSA (FiniteCFG Region)
open Silmaril.SSA.LambdaRTL (Val)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (PacketType PrimitiveSignature Code elaborateRow)
open scoped BigOperators

variable {F : Type} {blocks exits captures : Nat}
  {sig : PrimitiveSignature F} {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}
  {source : FiniteCFG F blocks exits captures}

/-- Each row either has a checked operand schedule or already belongs to
the public packet-scoped grammar. The latter needs no fresh labels. -/
inductive Row (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) (input : PacketType) (written : Region F)
  | scheduled (body : ScheduledTransfer sig packets outputs input written)
  | unchanged (body : Code sig (Sum.elim packets outputs) [input])
      (accepted : elaborateRow (Sum.elim packets outputs) sig [input] written = some body)

def Row.count {input : PacketType} {written : Region F} : Row sig packets outputs input written → Nat
  | .scheduled body => body.count
  | .unchanged .. => 0

structure Shape (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) (source : FiniteCFG F blocks exits captures) where
  start : Fin blocks
  seed : Val (Fin captures)
  entry_eq : source.entry.erase = .br start.val (packetTerm seed)
  row : ∀ i, Row sig packets outputs (packets i) (source.block i).erase

/-- Read each original row before relocating any label. If a row cannot
be scheduled, it must already elaborate in the public row grammar. -/
def read [DecidableEq F] (sig : PrimitiveSignature F) (packets : Fin blocks → PacketType)
    (outputs : Fin exits → PacketType) (source : FiniteCFG F blocks exits captures) :
    Option (Shape sig packets outputs source) := do
  let ⟨⟨start, seed⟩, entryEq⟩ ← readEntry source
  let rows ← tabulateDependent blocks fun i =>
    match readTransfer sig packets outputs (packets i) (source.block i) with
    | some body => some (.scheduled body)
    | none =>
      match h : elaborateRow (Sum.elim packets outputs) sig [packets i] (source.block i).erase with
      | some body => some (.unchanged body h)
      | none => none
  return ⟨start, seed, entryEq, rows⟩

def Shape.count (s : Shape sig packets outputs source) : Nat := ∑ i, (s.row i).count

/-- A fresh label is an original row index paired with a position in
that row's schedule, numbered in original row order after the old table. -/
def Shape.fresh (s : Shape sig packets outputs source) (i : Fin blocks) (j : Fin (s.row i).count) :
    Fin (blocks + s.count) :=
  freshLabel blocks (finSigmaFinEquiv ⟨i, j⟩)

def Row.head {freshCount : Nat} {input : PacketType} {written : Region F} (row : Row sig packets outputs input written)
    (labels : Fin row.count → Fin (blocks + freshCount)) : Region F :=
  match row with
  | .scheduled body => body.tree.entry (oldLabel freshCount) labels
  | .unchanged .. => written.renameLabels (moveExit blocks freshCount)

def Row.cell {freshCount : Nat} {input : PacketType} {written : Region F} (row : Row sig packets outputs input written)
    (labels : Fin row.count → Fin (blocks + freshCount)) : Fin row.count → PacketType × Region F :=
  match row with
  | .scheduled body => body.tree.cells (oldLabel freshCount) labels
  | .unchanged .. => Fin.elim0

/-- Old block indices and packet types are retained. Only the outward
labels move past the entire fresh suffix. -/
def Shape.table (s : Shape sig packets outputs source) : Fin (blocks + s.count) → PacketType × Region F :=
  appendTable (fun i => (packets i, (s.row i).head (s.fresh i))) fun j =>
    let owned := finSigmaFinEquiv.symm j
    (s.row owned.1).cell (s.fresh owned.1) owned.2

structure Emitted (s : Shape sig packets outputs source) where
  code : FiniteCFG F (blocks + s.count) exits captures
  entry_eq : code.entry.erase = source.entry.erase
  row_eq : ∀ i, (code.block i).erase = (s.table i).2

def emit (s : Shape sig packets outputs source) : Option (Emitted s) := do
  let labels := blocks + s.count + exits
  let entry ← scopedRow labels captures source.entry.erase
  let rows ← tabulateDependent (blocks + s.count) fun i => scopedRow labels (captures + 1) (s.table i).2
  return ⟨⟨entry.val, fun i => (rows i).val⟩, entry.property, fun i => (rows i).property⟩

structure Compiled (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  shape : Shape sig packets outputs source
  emitted : Emitted shape
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  emittedTyped : letI := sig.typing; emitted.code.HasType context (fun i => (shape.table i).1) outputs
  publicReadback : Constructed sig (fun i => (shape.table i).1) outputs emitted.code

/-- Schedule all supported transfers in one pass and check exact public
readback once at the final table and ordered exit profile. -/
def compile [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Compiled sig context packets outputs source) :=
  letI := sig.typing
  if original : NamedFlat.check source context packets outputs = true then
    match (read sig packets outputs source).bind fun shape => (emit shape).map (Sigma.mk shape) with
    | none => none
    | some ⟨shape, emitted⟩ =>
      let profile := fun i => (shape.table i).1
      if typed : NamedFlat.check emitted.code context profile outputs = true then
        (construct sig profile outputs emitted.code).map fun packed =>
          ⟨shape, emitted, NamedFlat.check_sound _ _ _ _ original, NamedFlat.check_sound _ _ _ _ typed, packed⟩
      else none
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed.Block.Graph

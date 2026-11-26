module

public import Silmaril.SSA.MLIR.CF.Basic.Defs

/-! Placement of one pure total floating node against the control and local
binding order of a typed CFG. Click, PLDI ’95, §§2.1–2.4. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block Cfg Terminator)
open Silmaril.MLIR.Pure (OpSignature)

abbrev Target (Label : List Width → Type) := Sigma Label

/-- The anonymous entry has ID `none`. Other blocks retain their typed label. -/
abbrev BlockId (Label : List Width → Type) := Option (Target Label)

/-- An occurrence in the source terminator. Both arms can target the same block. -/
inductive EdgeSlot where
  | jump
  | onTrue
  | onFalse
  deriving DecidableEq

structure BlockShape (Label : List Width → Type) where
  bindings : Nat
  target : EdgeSlot → Option (Target Label)

variable {Op : OpSignature} {Label : List Width → Type}
variable {Input Result : List Width}

/-- Count bindings and read successors from the existing typed CFG. -/
def shape (cfg : Cfg Op Label Input Result) : BlockId Label → BlockShape Label
  | none => ofBlock cfg.entry
  | some ⟨_, label⟩ => ofBlock (cfg.block label)
where
  ofBlock : {Δ : List Width} → Block Op Label Δ Result → BlockShape Label
    | _, .terminator term => ⟨0, targetAt term⟩
    | _, .letOp _ _ rest =>
      let tail := ofBlock rest
      ⟨tail.bindings + 1, tail.target⟩
  targetAt {Δ : List Width} : Terminator Label Result Δ → EdgeSlot → Option (Target Label)
    | .br edge, .jump | .condBr _ edge _, .onTrue | .condBr _ _ edge, .onFalse =>
      some ⟨_, edge.label⟩
    | _, _ => none

/-- A finite structural path from entry. The visited list is newest first.
Both arms of a conditional are possible edges for this analysis. -/
inductive EntryPath (cfg : Cfg Op Label Input Result) :
    BlockId Label → List (BlockId Label) → Prop where
  | entry : EntryPath cfg none [none]
  | step {src : BlockId Label} {past : List (BlockId Label)} {dst : Target Label}
      (path : EntryPath cfg src past) (slot : EdgeSlot)
      (edge : (shape cfg src).target slot = some dst) :
      EntryPath cfg (some dst) (some dst :: past)

def Reachable (cfg : Cfg Op Label Input Result) (b : BlockId Label) : Prop :=
  ∃ past, EntryPath cfg b past

def Dominates (cfg : Cfg Op Label Input Result) (a b : BlockId Label) : Prop :=
  ∀ past, EntryPath cfg b past → a ∈ past

/-- Supplied tree addresses with a sound reachability mask and a proof that
ancestry implies dominance on the underlying CFG. The tree may omit dominance
facts, in which case the checker can reject a legal placement. -/
structure DominatorTree (cfg : Cfg Op Label Input Result) where
  address : BlockId Label → List Nat
  entry_address : address none = []
  address_injective : ∀ {a b}, address a = address b → a = b
  reachable : BlockId Label → Bool
  reachable_sound : ∀ {b}, reachable b = true → Reachable cfg b
  prefix_sound : ∀ {a b}, Reachable cfg b → List.IsPrefix (address a) (address b) → Dominates cfg a b

/-- A cut after this many existing bindings. At a cut the operands already
defined there are available, an insertion runs next, then the original
instruction or terminator reads its inputs. -/
structure Point (Label : List Width → Type) where
  block : BlockId Label
  cut : Nat

inductive Use (Label : List Width → Type) where
  | ordinary (point : Point Label)
  | phi (source : BlockId Label) (slot : EdgeSlot) (argument : Nat)

/-- A Phi operand is a successor block argument read at the source terminator.
The branch occurrence must exist and carry the selected argument. -/
def Use.point? (cfg : Cfg Op Label Input Result) : Use Label → Option (Point Label)
  | .ordinary point => some point
  | .phi source slot argument => do
    let layout := shape cfg source
    let dst ← layout.target slot
    if argument < dst.1.length then some ⟨source, layout.bindings⟩ else none

variable {cfg : Cfg Op Label Input Result}

def Point.Valid (cfg : Cfg Op Label Input Result) (p : Point Label) : Prop :=
  Reachable cfg p.block ∧ p.cut ≤ (shape cfg p.block).bindings

/-- Control dominance and, if execution stays in one block, local availability. -/
structure Point.AvailableAt (cfg : Cfg Op Label Input Result) (defSite read : Point Label) : Prop where
  dominates : Dominates cfg defSite.block read.block
  local_order : defSite.block = read.block → defSite.cut ≤ read.cut

/-- Legality for the supplied operand locations and uses of one insertion. -/
structure Legal (cfg : Cfg Op Label Input Result) (operands : List (Point Label))
    (uses : List (Use Label)) (candidate : Point Label) : Prop where
  candidate_valid : candidate.Valid cfg
  operands_available : ∀ operand ∈ operands, operand.Valid cfg ∧ operand.AvailableAt cfg candidate
  uses_available : ∀ use ∈ uses, ∃ point, use.point? cfg = some point ∧
    point.Valid cfg ∧ candidate.AvailableAt cfg point

def Point.valid? (tree : DominatorTree cfg) (p : Point Label) : Bool :=
  tree.reachable p.block && decide (p.cut ≤ (shape cfg p.block).bindings)

/-- Ancestry tests the block constraint. The same-block condition tests local order. -/
def Point.available? (tree : DominatorTree cfg) (defSite read : Point Label) : Bool :=
  let a := tree.address defSite.block
  let b := tree.address read.block
  a.isPrefixOf b && decide (a = b → defSite.cut ≤ read.cut)

def checkPlacement (tree : DominatorTree cfg) (operands : List (Point Label))
    (uses : List (Use Label)) (candidate : Point Label) : Bool :=
  candidate.valid? tree &&
    operands.all (fun operand => operand.valid? tree && operand.available? tree candidate) &&
    uses.all (fun use => (use.point? cfg).any fun point =>
      point.valid? tree && candidate.available? tree point)

end Silmaril.SSA.SeaOfNodes.GCM

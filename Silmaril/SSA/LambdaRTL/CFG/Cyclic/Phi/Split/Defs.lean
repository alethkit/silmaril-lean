module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Defs
public import Silmaril.SSA.LambdaRTL.Nameless.Defs

/-! # Rename and split one normalized φ self-edge -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split

universe v w
variable {V W K J : Type w} {F : Type v}

/-- Register and block alignment for a split of the chosen header's self-edge.
The forwarding label is outside the image of the original block labels. -/
structure Plan (V W K J : Type w) where
  register : V ≃ W
  label : K ↪ J
  header : K
  forward : J
  fresh : ∀ k, label k ≠ forward

/-- Transport a source store along the register equivalence. -/
def Plan.renameStore (plan : Plan V W K J) {α : Type w} (store : V → α) : W → α :=
  store ∘ plan.register.symm

variable (plan : Plan V W K J) [DecidableEq K]

/-- Whether a pending edge is the selected self-edge. -/
def Plan.selected (source : Option K) (target : K) : Prop :=
  source = some plan.header ∧ target = plan.header

instance (source : Option K) (target : K) : Decidable (plan.selected source target) :=
  inferInstanceAs (Decidable (source = some plan.header ∧ target = plan.header))

/-- Replace the destination of just the selected branch. -/
def Plan.route (source : Option K) (target : Option K) : Option J :=
  target.map fun k => if plan.selected source k then plan.forward else plan.label k

/-- Replace the predecessor key of just the selected incoming column. -/
def Plan.rekey (target : K) (source : Option K) : Option J :=
  if plan.selected source target then some plan.forward else source.map plan.label

def Plan.renameTerm (route : Option K → Option J) : Term V (Option K) F → Term W (Option J) F
  | .br key value => .br (route key) (value.rename plan.register)
  | .case op x t y u =>
      .case (op.rename plan.register) (plan.register x) (renameTerm route t)
        (plan.register y) (renameTerm route u)

def Plan.renameBody (route : Option K → Option J) : Body V (Option K) F → Body W (Option J) F
  | .let1 x op body => .let1 (plan.register x) (op.rename plan.register) (renameBody route body)
  | .let2 x y op body =>
      .let2 (plan.register x) (plan.register y) (op.rename plan.register) (renameBody route body)
  | .term term => .term (plan.renameTerm route term)

def Plan.renameRow (target : K) (row : Row V K) : Row W J :=
  ⟨plan.register row.dst,
    row.incoming.map fun (pred, value) => (plan.rekey target pred, value.rename plan.register)⟩

def Plan.renameBlock (key : K) (block : Block V K F) : Block W J F :=
  ⟨block.rows.map (plan.renameRow key), plan.renameBody (plan.route (some key)) block.body⟩

def Plan.forwardBlock : Block W J F := ⟨[], .term (br (plan.label plan.header))⟩

/-- Insert the forwarding block at the old predecessor's position in the
table, immediately before the renamed header. This preserves incoming row
order while replacing the old self-edge key. The new block writes no registers. -/
def Plan.rewrite (source : Graph V K F) : Graph W J F :=
  ⟨plan.renameBody (plan.route none) source.entry,
    source.blocks.flatMap fun (key, block) =>
      let renamed := (plan.label key, plan.renameBlock key block)
      if key = plan.header then [(plan.forward, plan.forwardBlock), renamed] else [renamed]⟩

def Plan.hasBackedge (source : Graph V K F) : Bool :=
  (source.blocks.lookup plan.header).any fun block =>
    block.body.targets.contains (some plan.header)

deriving instance DecidableEq for Row
deriving instance DecidableEq for Block
deriving instance DecidableEq for Graph

variable [DecidableEq V] [DecidableEq W] [DecidableEq J]

/-- Check both graphs' normalization and that the candidate is precisely the
rename-and-split rewrite of an existing self-edge. -/
def Plan.check [DecidableEq F] (source : Graph V K F) (target : Graph W J F) : Bool :=
  source.check && plan.hasBackedge source && target.check && decide (target = plan.rewrite source)

/-- The syntax checks are separate from global and typed target admission. -/
structure Checked (source : Graph V K F) (target : Graph W J F) : Prop where
  sourceNormalized : source.check = true
  backedge : plan.hasBackedge source = true
  targetNormalized : target.check = true
  rewritten : target = plan.rewrite source

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split

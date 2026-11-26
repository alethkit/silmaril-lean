module

public import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Defs

/-! Discover and compose checked word-add and erasure edits on the current word suffix. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery

open Diamond (Ty ValueSort)
open ConstantFold
open GVN (Producer)
open SubZero (word)

variable {inputs : List (ValueSort Unit)} {ports : List (Ty Unit)}

inductive Rule where
  | literal
  | rightZero
  | deleteUnused
  deriving DecidableEq, Repr

def Rule.erases : Rule → Bool
  | .literal => false
  | .rightZero | .deleteUnused => true

def isAdd {ins : List (ValueSort Unit)} {out : ValueSort Unit} : SubZero.Opcode ins out → Bool
  | .add => true
  | _ => false

def addCount (block : Block inputs ports) : Nat :=
  (Deletion.opcodes block.flow).countP fun ⟨_, _, opcode⟩ => isAdd opcode

/-- Literal folds spend add operators. Erasures can spend bindings as well. -/
def weight (block : Block inputs ports) : Nat :=
  block.sigs.length + addCount block

structure Edit (block : Block inputs ports) where
  rule : Rule
  state : State inputs ports block.sigs
  bindingCount : state.block.sigs.length + (if rule.erases then 1 else 0) = block.sigs.length
  decreases : weight state.block < weight block

def checkedEdit? (block : Block inputs ports) (rule : Rule) (state : State inputs ports block.sigs) :
    Option (Edit block) :=
  if h : state.block.sigs.length + (if rule.erases then 1 else 0) = block.sigs.length ∧
      weight state.block < weight block then
    some ⟨rule, state, h.1, h.2⟩
  else none

def addRule? : AddIdealize.Rule → Option Rule
  | .literal => some .literal
  | .rightZero => some .rightZero
  | _ => none

/-- Let the ordered checker choose the rule at this producer before
restricting the result to literal folding and right-zero. -/
def add? (block : Block inputs ports) (candidate : Producer block.flow word) : Option (Edit block) :=
  match AddIdealize.step ⟨fun _ => none⟩ block.program candidate with
  | .ok (some applied) =>
    (addRule? applied.rule).bind fun rule => checkedEdit? block rule (fromRewrite block applied.rewrite)
  | _ => none

/-- Restrict the checked add decision to right-zero. -/
def rightZero? (block : Block inputs ports) (candidate : Producer block.flow word) : Option (Edit block) :=
  (add? block candidate).filter fun edit => decide (edit.rule = .rightZero)

/-- Attempt an erasure with the complete outgoing packet in scope. -/
def unused? (block : Block inputs ports) (candidate : Producer block.flow word) : Option (Edit block) :=
  (Deletion.delete? candidate block.packet).bind fun deleted =>
    checkedEdit? block .deleteUnused
      ⟨⟨deleted.erasure.sigs', deleted.erasure.flow, deleted.outputs⟩, deleted.erasure.route⟩

/-- Scan for an eligible add decision, then for an unused producer.
Each scan selects the first candidate in table order. -/
def step? (block : Block inputs ports) : Option (Edit block) :=
  let producers := RightIdentityPass.wordProducers block.flow
  (producers.findSome? (add? block)).orElse fun _ => producers.findSome? (unused? block)

def NoEligible (block : Block inputs ports) : Prop :=
  ∀ candidate : Producer block.flow word, add? block candidate = none ∧ unused? block candidate = none

structure Result (block : Block inputs ports) where
  state : State inputs ports block.sigs
  rules : List Rule

/-- Run with enough fuel for all possible edits and a final scan. The
weight check carries this budget invariant through every recursive step. -/
def run : (fuel : Nat) → (block : Block inputs ports) → weight block < fuel → Result block
  | 0, _, enough => (Nat.not_lt_zero _ enough).elim
  | fuel + 1, block, enough =>
    match step? block with
    | none => ⟨initial block, []⟩
    | some edit =>
      have decreases := edit.decreases
      let tail := run fuel edit.state.block (by omega)
      ⟨edit.state.compose tail.state, edit.rule :: tail.rules⟩

/-- Re-enumerate after each edit. The initial weight bounds
successful edits, with one extra unit of fuel for the last scan. -/
def normalize (block : Block inputs ports) : Result block :=
  run (weight block + 1) block (Nat.lt_succ_self _)

end Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery

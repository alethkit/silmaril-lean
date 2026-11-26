module

public import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Defs

/-! Discover and compose checked word-add and erasure edits on the current word suffix. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery

open Diamond (Dataflow Ty ValueSort dataPorts)
open ConstantFold
open GVN (Producer)
open SubZero (word)
open RVSDG (Wires)

variable {inputs : List (ValueSort Unit)} {ports : List (Ty Unit)}

inductive Rule where
  | literal
  | rightZero
  | literalRight
  | deleteUnused
  deriving DecidableEq, Repr

def Rule.erases : Rule → Bool
  | .literal | .literalRight => false
  | .rightZero | .deleteUnused => true

def isAdd {ins : List (ValueSort Unit)} {out : ValueSort Unit} : SubZero.Opcode ins out → Bool
  | .add => true
  | _ => false

def addCount (block : Block inputs ports) : Nat :=
  (Deletion.opcodes block.flow).countP fun ⟨_, _, opcode⟩ => isAdd opcode

def leftLiteral {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    (known : Literals args past) {ins : List (ValueSort Unit)} {out : ValueSort Unit} :
    SubZero.Opcode ins out → Wires args past (dataPorts ins) → Bool
  | .add, .cons lhs (.cons rhs .nil) => (known lhs).isSome && (known rhs).isNone
  | .literal _, _ | .sub, _ | .mul, _ => false

/-- Count adds with a known literal only on the left, using the same
ordered prefix facts as the add dispatcher. -/
def countLeftLiterals {args : List (Ty Unit)} : {past sigs : List (List (Ty Unit))} →
    RightSpine.Prefix args past → Dataflow SubZero.Opcode args past sigs → Nat
  | _, _, _, .nil => 0
  | _, _, known, .cons op operands rest =>
    (if leftLiteral known.literals op operands then 1 else 0) +
      countLeftLiterals (known.record op operands) rest

def leftLiteralCount (block : Block inputs ports) : Nat :=
  countLeftLiterals RightSpine.Prefix.empty block.flow

def primaryWeight (block : Block inputs ports) : Nat :=
  block.sigs.length + addCount block

/-- Encode primary weight and literal-left count in disjoint bands.
The literal-left count is bounded by the number of bindings. -/
def weight (block : Block inputs ports) : Nat :=
  primaryWeight block * primaryWeight block + leftLiteralCount block

/-- Swaps keep the primary counts and strictly improve operand order.
Folds and erasures must lower the primary measure. -/
abbrev Progress (rule : Rule) (before after : Block inputs ports) : Prop :=
  if rule = .literalRight then
    primaryWeight after = primaryWeight before ∧ leftLiteralCount after < leftLiteralCount before
  else primaryWeight after < primaryWeight before

structure Edit (block : Block inputs ports) where
  rule : Rule
  state : State inputs ports block.sigs
  bindingCount : state.block.sigs.length + (if rule.erases then 1 else 0) = block.sigs.length
  progress : Progress rule block state.block
  decreases : weight state.block < weight block

def checkedEdit? (block : Block inputs ports) (rule : Rule) (state : State inputs ports block.sigs) :
    Option (Edit block) :=
  if h : state.block.sigs.length + (if rule.erases then 1 else 0) = block.sigs.length ∧
      Progress rule block state.block ∧ weight state.block < weight block then
    some ⟨rule, state, h.1, h.2.1, h.2.2⟩
  else none

def addRule? : AddIdealize.Rule → Option Rule
  | .literal => some .literal
  | .rightZero => some .rightZero
  | .offSpineSwap => some .literalRight
  | _ => none

/-- Let the ordered checker choose the rule at this producer before
restricting the result to literal folding, right-zero and off-spine
literal-right commutation. No signed source IDs are supplied. -/
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

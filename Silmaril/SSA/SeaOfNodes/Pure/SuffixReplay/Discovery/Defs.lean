module

public import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Defs

/-! Discover and compose checked erasing edits on the current word suffix. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery

open Diamond (Ty ValueSort)
open ConstantFold
open GVN (Producer)
open SubZero (word)

variable {inputs : List (ValueSort Unit)} {ports : List (Ty Unit)}

inductive Rule where
  | rightZero
  | deleteUnused
  deriving DecidableEq, Repr

structure Edit (block : Block inputs ports) where
  rule : Rule
  state : State inputs ports block.sigs
  shorter : state.block.sigs.length + 1 = block.sigs.length

/-- Ask the ordered add checker first. Only an actual right-zero decision
that erases exactly one binding is eligible. -/
def rightZero? (block : Block inputs ports) (candidate : Producer block.flow word) : Option (Edit block) :=
  match AddIdealize.step ⟨fun _ => none⟩ block.program candidate with
  | .ok (some applied) =>
    if applied.rule = .rightZero then
      if h : applied.rewrite.sigs'.length + 1 = block.sigs.length then
        some ⟨.rightZero, fromRewrite block applied.rewrite, h⟩
      else none
    else none
  | _ => none

/-- Attempt one erasure with every outgoing occurrence still in the packet. -/
def unused? (block : Block inputs ports) (candidate : Producer block.flow word) : Option (Edit block) :=
  (Deletion.delete? candidate block.packet).map fun deleted =>
    ⟨.deleteUnused, ⟨⟨deleted.erasure.sigs', deleted.erasure.flow, deleted.outputs⟩, deleted.erasure.route⟩,
      deleted.erasure.shorter⟩

/-- Prefer right-zero. Within each scan, select the first producer in table order. -/
def step? (block : Block inputs ports) : Option (Edit block) :=
  let producers := RightIdentityPass.wordProducers block.flow
  (producers.findSome? (rightZero? block)).orElse fun _ => producers.findSome? (unused? block)

def NoEligible (block : Block inputs ports) : Prop :=
  ∀ candidate : Producer block.flow word, rightZero? block candidate = none ∧ unused? block candidate = none

structure Result (block : Block inputs ports) where
  state : State inputs ports block.sigs
  rules : List Rule

/-- Run with enough fuel for all possible erasures and a final scan. The
size check carries this budget invariant through every recursive step. -/
def run : (fuel : Nat) → (block : Block inputs ports) → block.sigs.length < fuel → Result block
  | 0, _, enough => (Nat.not_lt_zero _ enough).elim
  | fuel + 1, block, enough =>
    match step? block with
    | none => ⟨initial block, []⟩
    | some edit =>
      have smaller := edit.shorter
      let tail := run fuel edit.state.block (by omega)
      ⟨edit.state.compose tail.state, edit.rule :: tail.rules⟩

/-- Re-enumerate after each edit. The initial producer count bounds
successful edits, with one extra unit of fuel for the last scan. -/
def normalize (block : Block inputs ports) : Result block :=
  run (block.sigs.length + 1) block (Nat.lt_succ_self _)

end Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery

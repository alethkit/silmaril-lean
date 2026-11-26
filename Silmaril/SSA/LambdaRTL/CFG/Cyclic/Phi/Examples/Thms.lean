module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Thms
import Mathlib.Data.Nat.Pairing
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Defs
meta import Mathlib.Data.Nat.Pairing

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Examples

private def model : Model Unit Option Nat where
  unit := 0
  pair := Nat.pair
  inl := id
  inr := Nat.succ
  unpair value := some (Nat.unpair value)
  split
    | 0 => some (.inl 0)
    | n + 1 => some (.inr n)
  app _ := some
  abort _ := none

private def input : Nat → Nat
  | 0 => 2
  | 1 => 5
  | 2 => 1
  | _ => 0

-- Registers 0 and 1 are swapped on the backedge, 2 is the countdown,
-- and 3 is an ordinary live-in written in the predecessor and used after the swap.
private def header : Block Nat Nat Unit :=
  ⟨[⟨0, [(none, .var 0), (some 20, .var 1)]⟩, ⟨1, [(none, .var 1), (some 20, .var 0)]⟩],
    .term (.case (.val (.var 2)) 2 (ret (.pair (.var 0) (.pair (.var 1) (.var 3)))) 2 (br 20))⟩

private def latch : Block Nat Nat Unit :=
  ⟨[], .let1 3 (.val (.var 0)) (.term (br 10))⟩

private def graph : Graph Nat Nat Unit :=
  ⟨.term (br 10), [(10, header), (20, latch)]⟩

private def runFuel {State Result : Type} (step : State → Option (Result ⊕ State)) :
    Nat → State → Option Result
  | 0, _ => none
  | fuel + 1, state => do
      match ← step state with
      | .inl result => some result
      | .inr next => runFuel step fuel next

private def runSource : Option (Option Nat × Nat) :=
  execute model none graph.entry input >>= runFuel (step model graph) 4

private def runTarget : Option (Option Nat × Nat) := do
  let target ← compile graph
  let pending ← target.entry.evalJump model (inputEnv model input)
  runFuel (Cyclic.stepSSA model target.blocks (inputEnv model input)) 4 pending

-- Sequential φ assignment would put 5 in both registers, changing the second component.
example : runSource = some (none, Nat.pair 5 (Nat.pair 2 2)) := by decide
#guard runTarget == some (none, Nat.pair 5 (Nat.pair 2 2))

private def withRows (rows : List (Row Nat Nat)) : Graph Nat Nat Unit :=
  { graph with blocks := [(10, { header with rows }), (20, latch)] }

example : (compile (withRows [⟨0, [(some 20, .var 1), (none, .var 0)]⟩])).isNone := by decide
example : (compile (withRows [⟨0, [(none, .var 0)]⟩])).isNone := by decide
example : (compile (withRows [⟨0, [(none, .var 0), (none, .var 1)]⟩])).isNone := by decide
example : (compile (withRows [⟨0, [(none, .var 0), (some 99, .var 1)]⟩])).isNone := by decide
example : (compile (withRows (header.rows ++ header.rows))).isNone := by decide
example : (compile { graph with blocks := graph.blocks ++ [(10, header)] }).isNone := by decide
example : (compile { graph with entry := .term (br 99) }).isNone := by decide

-- Two syntactic edges from the entry to block 10 are ambiguous even at arity zero.
private def parallel : Graph Nat Nat Unit :=
  ⟨.term (.case (.val (.var 2)) 2 (br 10) 2 (br 10)), [(10, ⟨[], .term (ret .unit)⟩)]⟩

example : (compile parallel).isNone := by decide

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Examples

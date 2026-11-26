module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Correctness

/-! The emitted CF edges and full-buffer agreement with the activation driver. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF

open RVSDG (Tuple)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)

variable {cells : Nat} {args : List ValueSort}

/-- The real conditional terminator yields either the exit frame carrying
the word or the backedge frame. Both carry the post-store buffer in the monad. -/
theorem header_transition (graph : Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    Block.eval (evalBody input) ((lower cells graph).block Label.header) .nil initial =
      match observeActivation graph input initial with
      | .inl (word, final) => (.inl ⟨Label.exit, .cons word .nil⟩, final)
      | .inr next => (.inl ⟨Label.header, .nil⟩, next) :=
  Proofs.header_transition graph input initial

/-- The emitted CFG returns a word and entire buffer with at most the
given number of backedges precisely when the activation driver produces
them at a count within that allowance. -/
theorem run_eq_some_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (budget : Nat) (initial : Buffer cells) (result : Word × Buffer cells) :
    run graph input budget initial = some result ↔
      ∃ count ≤ budget, runAfter graph input count initial = some result :=
  Proofs.run_eq_some_iff graph input budget initial result

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF

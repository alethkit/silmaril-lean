module

public import Silmaril.Machine.SeaOfNodes.Diamond.RTL.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Diamond.RTL.Correctness

/-! # Return correspondence for the word diamond -/

public section

namespace Silmaril.Machine.SeaOfNodes.Diamond.RTL

open Silmaril.Machine.Lir (Memory Word)

variable {sigs : List (List PortTy)}

/-- The whole-program RTL return exists exactly for the source return word.
The RTL observation also fixes the result arity and preserves the input memory. -/
theorem lower_returns_iff (g : WordDiamond sigs) (x y : Word) (initial final : Memory)
    (returned : List Word) :
    (lower g).oracle 0 [x, y] initial returned final ↔
      ∃ value : Word, g.Returns model (entry x y) value ∧ returned = [value] ∧ final = initial :=
  Proofs.lower_returns_iff g x y initial final returned

/-- Every edge emitted by the lowering goes to a strictly greater block label. -/
theorem lower_forward (g : WordDiamond sigs) {source target : Nat}
    (h : target ∈ (lowerFunc g).succ source) : source < target :=
  Proofs.lower_forward g h

end Silmaril.Machine.SeaOfNodes.Diamond.RTL

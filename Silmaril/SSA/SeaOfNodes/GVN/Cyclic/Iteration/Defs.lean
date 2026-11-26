module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Defs

/-!
# Rebuild and repeat cyclic GVN

Each attempted step builds a view of the current typed loop. A successful
step removes one header binding. Failure returns the current loop, whether
the builder refused it or the admitted search found no shrinking candidate.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration

open Diamond (Signature Ty ValueSort)
open Deletion (DeletedLoop)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs : List (List (Ty Data))}
variable {out : ValueSort Data}

structure Result (Op : Signature.{u,v} Data)
    (inputs carried : List (ValueSort Data)) (entrySigs : List (List (Ty Data))) (out : ValueSort Data) where
  rewrite : DeletedLoop Op inputs carried entrySigs out
  deletions : Nat

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- Allow at most the given number of successful deletions. The builder
runs again on the new header and wires after each success. -/
def run : Nat → {headerSigs : List (List (Ty Data))} →
    Loop.Graph Op inputs carried entrySigs headerSigs out → Result Op inputs carried entrySigs out
  | 0, _, loop => ⟨⟨_, loop⟩, 0⟩
  | fuel + 1, _, loop =>
    match Builder.optimize? loop with
    | none => ⟨⟨_, loop⟩, 0⟩
    | some next =>
      let tail := run fuel next.graph
      { tail with deletions := tail.deletions + 1 }

/-- One unit of deletion fuel per original header binding. -/
def normalize {headerSigs : List (List (Ty Data))}
    (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) : Result Op inputs carried entrySigs out :=
  run headerSigs.length loop

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration

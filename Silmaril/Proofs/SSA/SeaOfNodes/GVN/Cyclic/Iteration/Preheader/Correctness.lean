module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader

open Silmaril.SSA.SeaOfNodes
open GVN.Cyclic.Iteration.Preheader
open GVN.Cyclic.Builder.Preheader (Native)
open Diamond (Ty ValueSort)

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit}

theorem run_entry (fuel : Nat) (loop : Native inputs carried entrySigs headerSigs out) :
    let final := (run fuel loop).rewrite.graph
    final.preheader = loop.preheader ∧ final.phiInputs .entry = loop.phiInputs .entry := by
  induction fuel generalizing headerSigs with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    cases found : GVN.Cyclic.Builder.Preheader.optimize? loop with
    | none =>
      rw [run_succ fuel loop, found]
      exact ⟨rfl, rfl⟩
    | some next =>
      have ⟨preheader, entry⟩ := GVN.Cyclic.Builder.Preheader.optimize_entry found
      have ⟨tailPreheader, tailEntry⟩ := ih next.graph
      rw [run_succ fuel loop, found]
      exact ⟨tailPreheader.trans preheader, tailEntry.trans entry⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader

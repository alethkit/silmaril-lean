module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Defs

/-! # A CFG shared by a continuation family -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region

open Silmaril.DeBruijn (lift)

universe u

/-- Run each continuation as the CFG entry, keeping the original blocks
independent of the continuation's newly bound payload. -/
def cfgContinuations {Φ : Type u} {n : Nat} (blocks : Fin n → Region Φ)
    (next : Nat → Region Φ) (i : Nat) : Region Φ :=
  .cfg (next i) n (fun j => (blocks j).renameVars (lift Nat.succ))

end Silmaril.Isotope.LambdaSSA.Region

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # The continuation family of a CFG -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region

open Silmaril.DeBruijn (lift)

universe u

/-- Start the original CFG at the label selected by the continuation, passing
its argument. The newly captured payload does not occur in the old blocks. -/
def cfgEntryContinuations {Φ : Type u} {n : Nat} (blocks : Fin n → Region Φ) (i : Nat) : Region Φ :=
  .cfg (.br i (.var 0)) n (fun j => (blocks j).renameVars (lift Nat.succ))

end Silmaril.Isotope.LambdaSSA.Region

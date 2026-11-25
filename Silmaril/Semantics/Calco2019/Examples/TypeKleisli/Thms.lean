module

public import Silmaril.Semantics.Calco2019.Examples.TypeKleisli.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.TypeKleisli

/-! # From function-level laws to the CALCO Kleisli interface -/

public section

namespace Silmaril.Calco2019.Examples.TypeKleisli

universe u

open CategoryTheory

variable {m : Type u → Type u} [_root_.Monad m] [LawfulMonad m]

/-- The inherited sums give the CALCO guarded Elgot bundle. Dinaturality follows
from the other equations by Proposition 17. -/
noncomputable def assemble {G : Guard m} (I : Iteration m G) :
    GuardedElgotMonad typeCoproducts :=
  Proofs.assemble I

end Silmaril.Calco2019.Examples.TypeKleisli

module

public import Silmaril.Semantics.Calco2019.Vacuous
import Silmaril.Proofs.Semantics.Calco2019.Vacuous

/-! # The initial guarded Elgot monad -/

public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  {T : CategoryTheory.Monad C} {S : GuardedElgotMonad P}

/-- Every monad morphism out of a vacuously guarded monad is guarded and preserves iteration. -/
noncomputable def vacuousMap (m : T ⟶ S.monad) : GuardedElgotMonadHom P (vacuousMonad P T) S where
  hom := m
  guarded := Proofs.vacuousMap_guarded m
  iteration := Proofs.vacuousMap_iterates m

/-- Initiality of the identity monad with the least guard, used before Corollary 29. -/
noncomputable def guardedIdentity_initial (P : Coproducts C) :
    IsInitial (guardedIdentity P) :=
  IsInitial.ofUniqueHom (fun S => vacuousMap (identityMonadMap S.monad))
    (fun _ f => GuardedElgotMonadHom.ext (Proofs.identityMap_unique f))

/-- The pure self-loop has a solution at any result object. Taking the
result to be initial gives the observation following Definition 19. -/
theorem GuardedElgotMonad.divergent_at (T : GuardedElgotMonad P) (h : T.IsElgot) (X Y : C) :
    Nonempty (X ⟶ T.monad.obj Y) :=
  Proofs.divergent_at T h X Y

end Silmaril.Calco2019

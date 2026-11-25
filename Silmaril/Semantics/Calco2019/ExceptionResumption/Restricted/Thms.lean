module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Restricted.Defs
public import Silmaril.Semantics.Calco2019.VacuousThms
import Silmaril.Proofs.Semantics.Calco2019.ResumptionRestricted

/-! # The restricted free extension statements of §1.3 -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)

/-- Over a total Elgot base, the resumption is the free extension by `H` in
the total Elgot category. The operation interpretation is unrestricted. -/
theorem freeExtension_total (total : T.IsElgot) (S : Maybe.TotalElgot P)
    (σ : H ⟶ (S.obj.monad : C ⥤ C)) (h : (⟨T, total⟩ : Maybe.TotalElgot P) ⟶ S) :
    ∃! k : (⟨(parametrizedElgot T H).resumptionElgotMonad R, resumption_isElgot T H R total⟩ :
        Maybe.TotalElgot P) ⟶ S,
      suspension T H R ≫ k.hom.hom.toNatTrans = σ ∧ baseEmbedding T H R ≫ k.hom = h.hom :=
  Proofs.free_restricted R (GuardedElgotMonad.IsElgot (P := P)) total (fun {_ _ _} => resumption_isElgot T H R total) S
    ⟨σ, GuardedElgotMonad.IsElgot.guardedNatTrans S.property σ⟩ h

/-- Over a guarded iterative base, the resumption is the free extension by `H`
in the guarded iterative category, for every guarded interpretation of the operations. -/
theorem freeExtension_iterative (iterative : T.guard.Iterative) (S : GuardedIterativeElgot P)
    (σ : GuardedTransformation H S.obj) (h : (⟨T, iterative⟩ : GuardedIterativeElgot P) ⟶ S) :
    ∃! k : (⟨(parametrizedElgot T H).resumptionElgotMonad R, resumption_iterative T H R iterative⟩ :
        GuardedIterativeElgot P) ⟶ S,
      suspension T H R ≫ k.hom.hom.toNatTrans = σ.val ∧ baseEmbedding T H R ≫ k.hom = h.hom :=
  Proofs.free_restricted R (fun S => S.guard.Iterative) iterative (fun {_ _} => resumption_iterative T H R iterative) S σ h

/-- The identity-base specialization freely adds guarded interpretations of `H`
among guarded iterative monads and guard-preserving monad morphisms. -/
theorem identityResumption_freeOn
    (R₀ : FinalResumptions (parametrizedElgot (guardedIdentity P) H).toParametrizedMonad)
    (S : GuardedIterativeElgot P) (σ : GuardedTransformation H S.obj) :
    ∃! k : (⟨(parametrizedElgot (guardedIdentity P) H).resumptionElgotMonad R₀,
        resumption_iterative (guardedIdentity P) H R₀ (Guardedness.vacuous_iterative)⟩ :
        GuardedIterativeElgot P) ⟶ S,
      suspension (guardedIdentity P) H R₀ ≫ k.hom.hom.toNatTrans = σ.val := by
  exact Proofs.identityResumption_freeOn R₀ S σ

end Silmaril.Calco2019.Exception

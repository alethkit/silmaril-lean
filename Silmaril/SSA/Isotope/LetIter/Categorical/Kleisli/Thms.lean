module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Categorical.Agreement
public import Silmaril.SSA.Isotope.LetIter.Categorical.AbortSequence.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Kleisli

/-! # Soundness of the set-valued Kleisli model for exact LetIter -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory Silmaril.Elgot
open Silmaril.Isotope.Semantics (BoundEnv)
open Silmaril.Isotope.LetIter.LocallyNameless

universe u v w q r

variable {α : Type u} [DecidableEq α] (F : α → Type (max u v))
  {m : Type (max u v) → Type (max u v)} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {Φ : Type q} [HasTy Φ (Ty α)] (M : Isotope.Semantics.InstructionModel (Ty.denote F) Φ m)
  {ν : Type w} [DecidableEq ν]

/-- With the standard set interpretation of free type syntax, every exact
typing derivation of a judgment gives the same Kleisli arrow. -/
theorem typingCoherent_ofType :
    letI := ofInstructionModel (Ty.denote F) M
    TypingCoherent (ν := ν) (Kleisli.Adjunction.toKleisli (ofTypeMonad m))
      (ofTypeModel (Ty.denote F)) Φ :=
  KleisliProofs.typingCoherent_ofType F M

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- Every native abort-extended equation preserves the Kleisli denotation at
arbitrary endpoint derivations. Bottom-effect instructions must be pure. -/
theorem denoteOfType_eq_of_abortEquiv {Γ : Ctx ν (Ty α)} {n : Nat} {β : BoundCtx (Ty α) n}
    {a b : Tm ν Φ n} {A : Ty α}
    (pureM : Isotope.Semantics.InstructionModel.RespectsPure (ε := ε) M)
    (h : AbortEquiv (⊥ : ε) Γ β a b A)
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    denoteOfType (Ty.denote F) M da = denoteOfType (Ty.denote F) M db :=
  KleisliProofs.denoteOfType_eq_of_abortEquiv F M pureM h da db

/-- Direct monadic evaluation preserves native abort-extended equations in
the empty free context, for every environment of the bound variables. -/
theorem denote_eq_of_abortEquiv_nil {n : Nat} {β : BoundCtx (Ty α) n}
    {a b : Tm Empty Φ n} {A : Ty α}
    (pureM : Isotope.Semantics.InstructionModel.RespectsPure (ε := ε) M)
    (h : AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) β a b A)
    (da : Derivation Φ .nil β a A) (db : Derivation Φ .nil β b A)
    (ρ : BoundEnv (Ty.denote F) β) :
    da.denote (Ty.denote F) M (fun x => x.elim) ρ =
      db.denote (Ty.denote F) M (fun x => x.elim) ρ :=
  KleisliProofs.denote_eq_of_abortEquiv_nil F M pureM h da db ρ

end Silmaril.Isotope.LetIter.Semantics.Categorical

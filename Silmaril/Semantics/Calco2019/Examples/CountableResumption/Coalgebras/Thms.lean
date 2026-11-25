module

public import Silmaril.Semantics.Calco2019.Examples.CountableResumption.Coalgebras.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.CountableResumptionCoalgebras

/-! # Initial and final countably nondeterministic resumptions -/

public section

universe u

namespace Silmaril.Calco2019.Examples.CountableResumption

open CategoryTheory CategoryTheory.Limits

variable {A : Type u} (B : A → Type u)

noncomputable def initial (X : Type u) : IsInitial (algebra B X) :=
  Proofs.initial B X

noncomputable def terminal (X : Type u) : IsTerminal (coalgebra B X) :=
  Proofs.terminal B X

/-- The initial-algebra construction gives the inductive monad on types. -/
noncomputable def inductiveResumptions : InitialResumptions (family B) where
  algebra := algebra B
  initial := initial B

/-- The final-coalgebra construction gives the coinductive monad on types. -/
noncomputable def coinductiveResumptions : FinalResumptions (family B) where
  coalgebra := coalgebra B
  final := terminal B

/-- Equality of coinductive computations is witnessed by a bisimulation of the I/O layers. -/
theorem bisim_iff {X : Type u} {p q : Coinductive B X} :
    p = q ↔ ∃ R : Coinductive B X → Coinductive B X → Prop, R p q ∧
      ∀ x y, R x y → Functor.Liftr R (QPF.Cofix.dest x) (QPF.Cofix.dest y) :=
  Proofs.bisim_iff B

theorem inductive_wellFounded (X : Type u) :
    WellFounded (Child B (X := X) (QPF.Fix.dest : Inductive B X → _)) :=
  Proofs.inductive_wellFounded B X

/-- The inductive resumption only has finite branches. -/
theorem inductive_no_infinite_branch (X : Type u) :
    IsEmpty {p : ℕ → Inductive B X // ∀ n, Child B QPF.Fix.dest (p (n + 1)) (p n)} :=
  wellFounded_iff_isEmpty_descending_chain.mp (inductive_wellFounded B X)

/-- Every unfolding of the repeated-action computation emits another action. -/
theorem forever_observe (X : Type u) (a : A) :
    QPF.Cofix.dest (forever B X a) =
      (pure (.inr ⟨a, fun _ => forever B X a⟩) : Choice (Step B X (Coinductive B X))) :=
  Proofs.forever_observe B X a

/-- With an available reply, repeatedly interacting gives an infinite branch. -/
theorem forever_infinite_branch (X : Type u) (a : A) (reply : B a) :
    ∃ p : ℕ → Coinductive B X, p 0 = forever B X a ∧
      ∀ n, Child B QPF.Cofix.dest (p (n + 1)) (p n) := by
  refine ⟨fun _ => forever B X a, rfl, fun _ => ⟨a, fun _ => forever B X a, ?_, reply, rfl⟩⟩
  rw [forever_observe]
  exact Elgot.Nondet.mem_pure _

theorem printingEquiv_natural (A Z W : Type u) (f : Z ⟶ W)
    (t : (signature (PrintingReply A)).obj Z) :
    printingEquiv A W ((signature (PrintingReply A)).map f t) =
      Prod.map id f (printingEquiv A Z t) := rfl

end Silmaril.Calco2019.Examples.CountableResumption

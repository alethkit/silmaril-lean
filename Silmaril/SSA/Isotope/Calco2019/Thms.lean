module

public import Silmaril.SSA.Isotope.Calco2019.Defs
import Silmaril.Proofs.SSA.Isotope.Calco2019.Institution

/-! # Denotation and satisfaction for the CALCO model of LetIter -/

public section

universe u v

namespace Silmaril.Isotope.Calco2019

open CategoryTheory
open Isotope.Semantics Isotope.LetIter.LocallyNameless Isotope.Institution
open Logic.Metatheory.TheoryModel

section Denotation

variable {τ : Type u} [TypeFormers τ] {ν : Type u} [DecidableEq ν]
  {ε : Type u} {P : InstrSig τ ε}
  (D : τ → Type v) [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]
  {Γ : Ctx ν τ}

/-- Exact loop denotation sequences the initial value with the CALCO solution. -/
theorem denote_iter (M : InstructionModel D P.Instr m) {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν P.Instr n} {b : Tm ν P.Instr (n + 1)} {A B : τ}
    (da : Derivation P.Instr Γ β a A)
    (db : Derivation P.Instr Γ (β.snoc A) b (coprod B A))
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    Derivation.denote D M (.iter da db) γ ρ =
      Derivation.denote D M da γ ρ >>= solve (fun x => do
        let s ← Derivation.denote D M db γ (ρ.snoc x)
        pure (CoproductModel.coprodEquiv (D := D) _ _ s)) := rfl

/-- The institution's structural denotation in the CALCO algebra is the program semantics. -/
theorem denote_algebra (M : InstructionModel D P.Instr m) {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν P.Instr n} {A : τ} (d : Derivation P.Instr Γ β t A) :
    Models.denote (denotationAlgebra D Γ M) d = Derivation.denote D M d :=
  Proofs.denote_algebra D M d

end Denotation

section Institution

variable {τ : Type u} [TypeFormers τ] {ν : Type u} [DecidableEq ν]
  {ε : Type u} {P Q : InstrSig τ ε}
  (D : τ → Type u) [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {m : Type u → Type u} [Monad m] [LawfulMonad m] [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]
  {Γ : Ctx ν τ}

/-- Satisfaction of an exact LetIter equation in this room is pointwise equality
of the original monadic denotations at all free and bound environments. -/
theorem sat_iff_denote (M : InstructionModel D P.Instr m) {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν P.Instr n} {A : τ} (da : Derivation P.Instr Γ β a A)
    (db : Derivation P.Instr Γ β b A) :
    ((Institution.LetIter.inst (ε := ε) Γ).obj P).Sat (denotationAlgebra D Γ M)
      ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩ ↔
      ∀ γ ρ, Derivation.denote D M da γ ρ = Derivation.denote D M db γ ρ := by
  rw [Institution.LetIter.sat_iff, denote_algebra, denote_algebra]
  exact ⟨fun h γ ρ => congrFun (congrFun h γ) ρ, fun h => funext fun γ => funext (h γ)⟩

/-- The model reduct in the existing institution is restriction of the primitive
interpretation. The carrier, sequencing and CALCO iteration are shared. -/
theorem reduct_algebra (g : P ⟶ Q) (M : InstructionModel D Q.Instr m) :
    (((Institution.LetIter.inst (ε := ε) Γ).map g).mod.obj (denotationAlgebra D Γ M)) =
      denotationAlgebra D Γ (reductInstructions D g M) :=
  Proofs.reduct_algebra D g M

/-- Satisfaction commutes with translating a sentence and restricting the instructions. -/
theorem satisfaction_change (g : P ⟶ Q) (M : InstructionModel D Q.Instr m)
    (e : ((Institution.LetIter.inst (ε := ε) Γ).obj P).Sen) :
    ((Institution.LetIter.inst (ε := ε) Γ).obj Q).Sat (denotationAlgebra D Γ M)
      (((Institution.LetIter.inst (ε := ε) Γ).map g).sen e) ↔
    ((Institution.LetIter.inst (ε := ε) Γ).obj P).Sat
      (denotationAlgebra D Γ (reductInstructions D g M)) e := by
  exact (Institution.LetIter.satisfaction Γ g (denotationAlgebra D Γ M) e).trans
    (Iff.of_eq (congrArg
      (fun N : ((Institution.LetIter.inst (ε := ε) Γ).obj P).Mod =>
        ((Institution.LetIter.inst (ε := ε) Γ).obj P).Sat N e)
      (reduct_algebra (Γ := Γ) D g M)))

end Institution

end Silmaril.Isotope.Calco2019

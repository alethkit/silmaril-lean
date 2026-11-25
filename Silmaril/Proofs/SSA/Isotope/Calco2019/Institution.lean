module

public import Silmaril.SSA.Isotope.Calco2019.Defs

public section

universe u v

namespace Silmaril.Isotope.Calco2019.Proofs

open CategoryTheory Logic.Metatheory.TheoryModel
open Isotope.Semantics Isotope.LetIter.LocallyNameless Isotope.Institution Isotope.Theory

variable {τ : Type u} [TypeFormers τ] {ν : Type u} [DecidableEq ν]
  {ε : Type u} {P Q : InstrSig τ ε}
  (D : τ → Type v) [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]
  {Γ : Ctx ν τ}

theorem denote_algebra (M : InstructionModel D P.Instr m) {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν P.Instr n} {A : τ} (d : Derivation P.Instr Γ β t A) :
    Models.denote (denotationAlgebra D Γ M) d = Derivation.denote D M d := by
  induction d <;> simp only [Models.denote, Derivation.denote, *] <;> rfl

private theorem reduct_op (M : InstructionModel D Q.Instr m) {n : Nat}
    {β : BoundCtx τ n} {A B : τ} (f : Q.Instr)
    (ht : instrTrg f = A) (hs : instrSrc f = B)
    (a : FreeEnv D Γ → BoundEnv D β → m (D B))
    (args : (j : Fin ((Models.signature Q.Instr Γ).arity
      (castOp (Models.signature Q.Instr Γ)
        (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex τ)) ht) (Models.Operation.op f)))) →
      (denotationAlgebra D Γ M).Carrier ((Models.signature Q.Instr Γ).argSort
        (castOp (Models.signature Q.Instr Γ)
          (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex τ)) ht) (Models.Operation.op f)) j))
    (hargs : ∀ j, HEq (args j) a) :
    (denotationAlgebra D Γ M).op
        (castOp (Models.signature Q.Instr Γ)
          (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex τ)) ht) (Models.Operation.op f)) args =
      fun γ ρ => a γ ρ >>= fun x =>
        cast (congrArg (fun A => m (D A)) ht)
          (M.eval f (cast (congrArg D hs.symm) x)) := by
  subst A
  subst B
  change (fun γ ρ => args (0 : Fin 1) γ ρ >>= M.eval f) = _
  exact congrArg (fun k γ ρ => k γ ρ >>= M.eval f) (eq_of_heq (hargs (0 : Fin 1)))

theorem reduct_algebra (g : P ⟶ Q) (M : InstructionModel D Q.Instr m) :
    Algebra.reductObj (Institution.LetIter.sigHom Γ g) (denotationAlgebra D Γ M) =
      denotationAlgebra D Γ (reductInstructions D g M) := by
  unfold Algebra.reductObj
  congr 1
  funext i o args
  cases o with
  | op f =>
    refine reduct_op D M (g.instr f) (g.target f) (g.source f) (args 0) _ (fun j =>
      (eqRec_heq _ _).trans ?_)
    let k : Fin 1 := (Institution.LetIter.sigHom Γ g).arg (.op f) j
    change HEq (args k) (args (0 : Fin 1))
    rw [Fin.eq_zero k]
  | fv | bv | let₁ | unit | pair | let₂ | inl | inr | case | abort | iter => rfl

end Silmaril.Isotope.Calco2019.Proofs

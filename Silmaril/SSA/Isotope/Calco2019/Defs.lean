module

public import Silmaril.Semantics.Calco2019.CompleteElgot.Thms
public import Silmaril.SSA.Isotope.Thms
public import Silmaril.SSA.Isotope.Institution.Thms

/-! # CALCO's complete Elgot iteration in exact LetIter -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.Calco2019

open Silmaril.Calco2019 Isotope.Semantics
open Isotope.LetIter.LocallyNameless
open Isotope.Institution
open Logic.Metatheory.TheoryModel
open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {ν : Type u} [DecidableEq ν]
  {ε : Type u} {P : InstrSig τ ε}
  (D : τ → Type v) [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {m : Type v → Type v} [Monad m] [LawfulMonad m] [Elgot.Iterate m] [Elgot.LawfulElgotMonad m]

/-- Solve a sum-valued body with the total CALCO guard and evaluate the resulting arrow. -/
noncomputable def solve {A B : Type v} (body : A → m (B ⊕ A)) : A → m B :=
  ((ofLawfulMonad m).iteration.iterate (computation m body) trivial).of

/-- The constructor algebra on environment-indexed computations. Every exact LetIter
sentence can be evaluated here. Its iteration constructor uses the CALCO solution. -/
noncomputable def denotationAlgebra (Γ : Ctx ν τ) (M : InstructionModel D P.Instr m) :
    Algebra (Models.signature P.Instr Γ) where
  Carrier i := FreeEnv D Γ → BoundEnv D i.bound → m (D i.result)
  op
    | .fv h, _ => fun γ _ => pure (γ _ _ h)
    | .bv i, _ => fun _ ρ => pure (ρ i)
    | .op f, a => fun γ ρ => a 0 γ ρ >>= M.eval f
    | .let₁ _ _, a => fun γ ρ => a 0 γ ρ >>= fun x => a 1 γ (ρ.snoc x)
    | .unit, _ => fun _ _ => pure ((UnitModel.unitEquiv (D := D)).symm PUnit.unit)
    | .pair _ _, a => fun γ ρ => do
        let x ← a 0 γ ρ
        let y ← a 1 γ ρ
        pure ((ProductModel.productEquiv (D := D) _ _).symm (x, y))
    | .let₂ _ _ _, a => fun γ ρ => do
        let xy ← a 0 γ ρ
        let (x, y) := ProductModel.productEquiv (D := D) _ _ xy
        a 1 γ ((ρ.snoc x).snoc y)
    | .inl _ _, a => fun γ ρ => do
        let x ← a 0 γ ρ
        pure ((CoproductModel.coprodEquiv (D := D) _ _).symm (.inl x))
    | .inr _ _, a => fun γ ρ => do
        let y ← a 0 γ ρ
        pure ((CoproductModel.coprodEquiv (D := D) _ _).symm (.inr y))
    | .case _ _ _, a => fun γ ρ => do
        let xy ← a 0 γ ρ
        match CoproductModel.coprodEquiv (D := D) _ _ xy with
        | .inl x => a 1 γ (ρ.snoc x)
        | .inr y => a 2 γ (ρ.snoc y)
    | .abort _, a => fun γ ρ => a 0 γ ρ >>= fun z =>
        PEmpty.elim (EmptyModel.emptyEquiv (D := D) z)
    | .iter _ _, a => fun γ ρ => a 0 γ ρ >>= solve (fun x => do
        let s ← a 1 γ (ρ.snoc x)
        pure (CoproductModel.coprodEquiv (D := D) _ _ s))

/-- Interpret a source instruction through a target model, transporting the input
and output along the source and target equalities of the signature map. -/
def reductInstructions {Q : InstrSig τ ε} (g : P ⟶ Q)
    (M : InstructionModel D Q.Instr m) : InstructionModel D P.Instr m where
  eval f x := cast (congrArg (fun A => m (D A)) (g.target f))
    (M.eval (g.instr f) (cast (congrArg D (g.source f).symm) x))

end Silmaril.Isotope.Calco2019

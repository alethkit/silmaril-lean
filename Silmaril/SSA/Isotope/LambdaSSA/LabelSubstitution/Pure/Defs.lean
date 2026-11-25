module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Purity.Thms

/-! # Semantic purity at exactly typed branch arguments -/

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]
  {m : Type v → Type v} [Monad m] {Φ : Type q} [HasTy Φ τ]
  (ε : Type r) [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε m]

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Exact typing with a pure denotation of each branch argument, including
branches in local blocks. Let expressions and case scrutinees can have effects. -/
inductive PureBranches : VCtx τ → Region Φ → LCtx τ → Prop where
  | br (h : At L i A) {ha : Tm.HasType Γ a A} {value : Env Γ → TyDen A}
      (pureArgument : Denotes (m := m) ε ha (fun ρ => pure (value ρ))) :
      PureBranches Γ (.br i a) L
  | let₁ (ha : Tm.HasType Γ a A) (hr : PureBranches (A :: Γ) rest L) :
      PureBranches Γ (.let₁ a rest) L
  | let₂ (ha : Tm.HasType Γ a (Silmaril.product A B))
      (hr : PureBranches (B :: A :: Γ) rest L) :
      PureBranches Γ (.let₂ a rest) L
  | case (ha : Tm.HasType Γ a (Silmaril.coprod A B))
      (left : PureBranches (A :: Γ) l L) (right : PureBranches (B :: Γ) r L) :
      PureBranches Γ (.case a l r) L
  | cfg {n : Nat} (R : Fin n → τ) {entry : Region Φ} {blocks : Fin n → Region Φ}
      (he : PureBranches Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, PureBranches (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
      PureBranches Γ (.cfg entry n blocks) L

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic

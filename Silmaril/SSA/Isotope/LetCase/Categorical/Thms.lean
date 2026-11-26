module

public import Silmaril.SSA.Isotope.LetCase.Categorical.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
import Silmaril.Proofs.SSA.Isotope.LetCase.Categorical.Sequencing

/-! # The exact LetCase continuation law -/

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetCase.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits PremonoidalCategory
open scoped MonoidalCategory
open LetCase.LocallyNameless
open LetIter.Semantics.Categorical (TypeModel InstructionModel envObj envSnocIso envRenameMap dropSlot)
open LetIter.ProofRelevant.Semantics.Categorical (duplicate)

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "Env" => envObj M Γ
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

/-- Renaming reads the old environment through the corresponding value map. -/
theorem denote_rename {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A) (ρ : BoundCtx.Renaming β δ) :
    denote J M (d.rename ρ) = J.map (envRenameMap M Γ ρ) ≫ denote J M d :=
  denote_rename_proof J M d ρ

/-- Below the newest binder, projection drops the arm payload and retains the result,
even when the continuation is effectful. -/
theorem denote_underBinder {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ (n + 1)}
    {X Y A : τ} (d : Derivation Φ Γ (β.snoc Y) t A) :
    J.map (envSnocIso M Γ (β.snoc X) Y).hom ≫ denote J M (d.underBinder (X := X)) =
      J.map (dropSlot M β X ▷ M.obj Y) ≫ J.map (envSnocIso M Γ β Y).hom ≫ denote J M d :=
  denote_underBinder_proof J M d

/-- Exact `bindLetCase` at the supplied typing witnesses. Centrality of the transported
context diagonal licenses retaining that context while moving the continuation. -/
theorem denote_bindLetCase {n : Nat} {β : BoundCtx τ n} {e : Tm ν Φ n}
    {l r k : Tm ν Φ (n + 1)} {A B D E : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (de : Derivation Φ Γ β e (coprod A B))
    (dl : Derivation Φ Γ (β.snoc A) l D) (dr : Derivation Φ Γ (β.snoc B) r D)
    (dk : Derivation Φ Γ (β.snoc D) k E) :
    denote J M (.let₁ (.case de dl dr) dk) =
      denote J M (.case de (.let₁ dl dk.underBinder) (.let₁ dr dk.underBinder)) :=
  denote_bindLetCase_proof J M central de dl dr dk

/-- A shared tensor at the original environment supplies its central diagonal. -/
theorem denote_bindLetCase_of_sharedTensor {n : Nat} {β : BoundCtx τ n} {e : Tm ν Φ n}
    {l r k : Tm ν Φ (n + 1)} {A B D E : τ}
    (h : J.obj (Env β) ⊗ J.obj (Env β) = J.obj (Env β ⊗ Env β))
    (shared : tensorIso (Env β) (Env β) = eqToIso h)
    (de : Derivation Φ Γ β e (coprod A B))
    (dl : Derivation Φ Γ (β.snoc A) l D) (dr : Derivation Φ Γ (β.snoc B) r D)
    (dk : Derivation Φ Γ (β.snoc D) k E) :
    denote J M (.let₁ (.case de dl dr) dk) =
      denote J M (.case de (.let₁ dl dk.underBinder) (.let₁ dr dk.underBinder)) :=
  denote_bindLetCase J M
    (LetIter.Semantics.Categorical.duplicate_central_of_tensor_eqToIso J (Env β) h shared) de dl dr dk

/-- Coherence lets the same law be stated for independently chosen derivations
of the two exact endpoint terms. -/
theorem denote_bindLetCase_of_coherent {n : Nat} {β : BoundCtx τ n} {e : Tm ν Φ n}
    {l r k : Tm ν Φ (n + 1)} {A B D E : τ}
    (coherent : TypingCoherent J M ν Φ)
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (de : Derivation Φ Γ β e (coprod A B))
    (dl : Derivation Φ Γ (β.snoc A) l D) (dr : Derivation Φ Γ (β.snoc B) r D)
    (dk : Derivation Φ Γ (β.snoc D) k E)
    (lhs : Derivation Φ Γ β (.let₁ (.case e l r) k) E)
    (rhs : Derivation Φ Γ β (.case e (.let₁ l k.underBinder) (.let₁ r k.underBinder)) E) :
    denote J M lhs = denote J M rhs :=
  (coherent lhs _).trans ((denote_bindLetCase J M central de dl dr dk).trans (coherent _ rhs))

end Silmaril.Isotope.LetCase.Semantics.Categorical

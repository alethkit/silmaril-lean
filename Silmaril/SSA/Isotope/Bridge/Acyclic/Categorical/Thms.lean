module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Thms
public import Silmaril.SSA.Isotope.LetCase.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Categorical

/-! # The categorical continuation law on compiled single-exit code -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Code

open CategoryTheory CategoryTheory.Limits PremonoidalCategory
open scoped MonoidalCategory
open LetIter.Semantics.Categorical (TypeModel InstructionModel envObj)
open LetIter.ProofRelevant.Semantics.Categorical (duplicate)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "Env" => envObj M (Ctx.nil : Ctx Empty τ)
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)
local notation "denote" => LetCase.Semantics.Categorical.denote J M

/-- A shared join and its copies in the two arms translate to equal LetCase
arrows. The compared endpoints are the actual translations of exact code. -/
theorem denote_distributeJoin {n : Nat} {β : BoundCtx τ n} {A B D E : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (e : Operand Φ β (coprod A B)) (l : Code Φ (β.snoc A) D) (r : Code Φ (β.snoc B) D)
    (k : Code Φ (β.snoc D) E) :
    denote (toLetCase (.join (.case e l r) k)).2 =
      denote (distributeJoin e l r k).toLetCase.2 :=
  denote_distributeJoin_proof J M central e l r k

end Silmaril.Isotope.LambdaSSA.Acyclic.Code

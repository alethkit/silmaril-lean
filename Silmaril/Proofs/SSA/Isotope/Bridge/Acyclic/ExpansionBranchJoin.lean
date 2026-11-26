module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.BranchJoin.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open LambdaSSA.Acyclic (Code Operand)
open LetIter.Semantics.Categorical (TypeModel InstructionModel envObj)
open LetIter.ProofRelevant.Semantics.Categorical (duplicate)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C} [DistributiveFreydCategory J] {M : TypeModel τ V}
  {n : Nat} {β : BoundCtx τ n} {A B D E : τ}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "Env" => envObj M Γ₀ β
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

theorem freydCaseAlgebra_sat_sharedJoin_proof (I : InstructionModel J M P.Instr)
    (central : IsCentral (J.map (duplicate Env) ≫ (tensorIso Env Env).inv))
    (e : Operand P.Instr β (coprod A B))
    (l : Code P.Instr (β.snoc A) D) (r : Code P.Instr (β.snoc B) D)
    (k : Code P.Instr (β.snoc D) E) :
    ((LetCase.inst Γ₀).obj P).Sat (freydCaseAlgebra J M I) (compile (sharedJoinEquation e l r k)) := by
  let left := (Code.join (.case e l r) k).toLetCase.2
  let right := (Code.distributeJoin e l r k).toLetCase.2
  let _ := I
  apply (LetCase.sat_iff Γ₀ P _ left right).mpr
  rw [freydCaseAlgebra_denote, freydCaseAlgebra_denote]
  exact Code.denote_distributeJoin J M central e l r k

end Silmaril.Isotope.Institution.Acyclic

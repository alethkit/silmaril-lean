module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.BranchJoin.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.ExpansionBranchJoin

/-! # Branch/join satisfaction before and after expansion -/

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open LambdaSSA.Acyclic (Code Operand)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent)
open LetIter.Semantics.Categorical (TypeModel InstructionModel envObj)
open LetIter.ProofRelevant.Semantics.Categorical (duplicate)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C} {M : TypeModel τ V}
  {n : Nat} {β : BoundCtx τ n} {A B D E : τ}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "Env" => envObj M Γ₀ β
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

/-- The two compiled terms have equal algebra folds by case/continuation
coherence under the branch payload binder. This calculation uses no iteration. -/
theorem freydCaseAlgebra_sat_sharedJoin [DistributiveFreydCategory J]
    (I : InstructionModel J M P.Instr)
    (central : IsCentral (J.map (duplicate Env) ≫ (tensorIso Env Env).inv))
    (e : Operand P.Instr β (coprod A B))
    (l : Code P.Instr (β.snoc A) D) (r : Code P.Instr (β.snoc B) D)
    (k : Code P.Instr (β.snoc D) E) :
    ((LetCase.inst Γ₀).obj P).Sat (freydCaseAlgebra J M I) (compile (sharedJoinEquation e l r k)) :=
  freydCaseAlgebra_sat_sharedJoin_proof I central e l r k

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]

/-- The expanded model satisfies the equation between the actual λSSA regions:
one has a shared block and the other has a local block in each arm. -/
theorem expandFreyd_sat_sharedJoin (I : InstructionModel J M P.Instr)
    (coherent : letI := I; RegionTypingCoherent (Φ := P.Instr) J M)
    (central : IsCentral (J.map (duplicate Env) ≫ (tensorIso Env Env).inv))
    (e : Operand P.Instr β (coprod A B))
    (l : Code P.Instr (β.snoc A) D) (r : Code P.Instr (β.snoc B) D)
    (k : Code P.Instr (β.snoc D) E) :
    (ssaRoom J P).Sat (ShrinkHoms.toShrinkHoms (Discrete.mk (expandFreyd J M I coherent)))
      (sharedJoinEquation e l r k) :=
  (sat_compile_iff (expandFreyd J M I coherent) _).mp
    (freydCaseAlgebra_sat_sharedJoin I central e l r k)

end Silmaril.Isotope.Institution.Acyclic

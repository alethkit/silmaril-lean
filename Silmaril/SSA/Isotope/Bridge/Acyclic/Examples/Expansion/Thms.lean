module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.BranchJoin.Thms
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-! # Expansion of a case with a shared primitive continuation -/

namespace Silmaril.Isotope.Institution.Acyclic.Examples

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open LambdaSSA.Acyclic (Code Operand)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent)
open LetIter.Semantics.Categorical (TypeModel InstructionModel envObj)
open LetIter.ProofRelevant.Semantics.Categorical (duplicate)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}

private abbrev ctx (A : τ) : BoundCtx τ 1 := .snoc .nil (coprod A A)

private def test (A : τ) : Operand P.Instr (ctx A) (coprod A A) := ⟨.bv 0, .bv⟩

private def arm (A : τ) : Code P.Instr ((ctx A).snoc A) A := .br ⟨.bv 0, .bv⟩

private def block (f : P.Instr) :
    Code P.Instr ((ctx (instrSrc f : τ)).snoc (instrSrc f)) (instrTrg f) :=
  .br ⟨.op f (.bv 0), .op .bv⟩

private def diamond (f : P.Instr) : SSAEquation P :=
  sharedJoinEquation (test (instrSrc f)) (arm (instrSrc f)) (arm (instrSrc f)) (block f)

-- Both arms send the payload to a nonempty CFG, whose single block runs f.
example (f : P.Instr) : ((diamond f).2.1).toSSA 0 =
    .cfg (.case (.var 0) (.br 0 (.var 0)) (.br 0 (.var 0))) 1
      (fun _ => .br 1 (.op f (.var 0))) := rfl

-- After distribution, each arm has its own local block and still applies f to
-- the passed result rather than to the carried case payload.
example (f : P.Instr) : ((diamond f).2.2).toSSA 0 =
    .case (.var 0)
      (.cfg (.br 0 (.var 0)) 1 (fun _ => .br 1 (.op f (.var 0))))
      (.cfg (.br 0 (.var 0)) 1 (fun _ => .br 1 (.op f (.var 0)))) := rfl

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C} {M : TypeModel τ V}
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

-- Read the primitive back from the algebra and evaluate the actual SSA equation.
example (f : P.Instr) (I : InstructionModel J M P.Instr)
    (coherent : letI := readInstructions J M (freydCaseAlgebra J M I) rfl
                RegionTypingCoherent (Φ := P.Instr) J M)
    (central : let env := envObj M Γ₀ (ctx (instrSrc f : τ))
               IsCentral (J.map (duplicate env) ≫ (tensorIso env env).inv)) :
    (ssaRoom J P).Sat (ShrinkHoms.toShrinkHoms (Discrete.mk
      (expandAlgebra J M (freydCaseAlgebra J M I) rfl coherent))) (diamond f) :=
  expandFreyd_sat_sharedJoin _ coherent central _ _ _ _

-- An ambient operation on every coproduct loop cannot be supplied on total
-- functions, even before requiring the Elgot laws.
example : IsEmpty (Iteration (Type : Type 1)) :=
  ⟨fun h => PEmpty.elim ((h.iterate (X := PUnit) (Y := PEmpty) coprod.inr) PUnit.unit)⟩

end Silmaril.Isotope.Institution.Acyclic.Examples

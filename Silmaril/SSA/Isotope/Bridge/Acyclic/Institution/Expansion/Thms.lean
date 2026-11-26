module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Expansion

/-! # The image of the exact SSA model reduct -/

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Acyclic (Code)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C} {M : TypeModel τ V}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

section Freyd

variable [DistributiveFreydCategory J]

/-- For the chosen type interpretation, turning primitive arrows into exact
LetCase operations and reading them back preserves those arrows. -/
@[simp] theorem readInstructions_freyd (I : InstructionModel J M P.Instr) :
    readInstructions J M (freydCaseAlgebra J M I) rfl = I :=
  readInstructions_freyd_proof M I

/-- With the arrow carriers fixed, an operation algebra is induced by a Freyd
interpretation exactly when all operations agree with the readback interpretation.
This test uses no iteration. -/
theorem freydPresentation_iff (A : CaseAlgebra P) (h : A.Carrier = freydCaseArrow J M) :
    (∃ I, freydCaseAlgebra J M I = A) ↔
      freydCaseAlgebra J M (readInstructions J M A h) = A :=
  freydPresentation_iff_proof M A h

end Freyd

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

/-- In a fixed strong Elgot ambient model, actual expansion is equivalent to
a Freyd presentation whose recovered primitive arrows satisfy region typing coherence. -/
theorem exactExpansion_iff (A : CaseAlgebra P) :
    (∃ K : CoherentRegionModel J P, K.caseAlgebra = A) ↔
      ∃ (M : TypeModel τ V) (h : A.Carrier = freydCaseArrow J M),
        freydCaseAlgebra J M (readInstructions J M A h) = A ∧
        (letI := readInstructions J M A h; RegionTypingCoherent (Φ := P.Instr) J M) :=
  exactExpansion_iff_proof A

/-- The model reduct of the chosen expansion is its original categorical
LetCase algebra. -/
@[simp] theorem expandFreyd_caseAlgebra (I : InstructionModel J M P.Instr)
    (coherent : letI := I; RegionTypingCoherent (Φ := P.Instr) J M) :
    (expandFreyd J M I coherent).caseAlgebra = freydCaseAlgebra J M I :=
  rfl

variable [FreydCategory.CentralUnit J]

/-- In the coherent expansion, the selected region arrow agrees with the
iteration-free interpretation on the very same input and exit objects. -/
theorem expandFreyd_denote (I : InstructionModel J M P.Instr)
    (coherent : letI := I; RegionTypingCoherent (Φ := P.Instr) J M)
    {n : Nat} {β : BoundCtx τ n} {A : τ} (c : Code P.Instr β A) :
    (expandFreyd J M I coherent).denoteSSA c = denoteAcyclic J M I c := by
  let _ := I
  let _ := coherent
  exact Code.denote_toSSA J M c (L := [A]) (exit := 0) rfl

/-- When the recovered interpretation presents the original algebra, the
corridor model functor sends the constructed expansion back to that algebra. -/
theorem expandAlgebra_reduct (A : CaseAlgebra P) (h : A.Carrier = freydCaseArrow J M)
    (coherent : letI := readInstructions J M A h; RegionTypingCoherent (Φ := P.Instr) J M)
    (presentation : freydCaseAlgebra J M (readInstructions J M A h) = A) :
    (reifyCorridor J P).mod.obj (ShrinkHoms.toShrinkHoms (Discrete.mk (expandAlgebra J M A h coherent))) =
      A :=
  presentation

/-- The constructed expansion preserves and reflects each exact equation of
the presented algebra. -/
theorem sat_expandAlgebra_iff (A : CaseAlgebra P) (h : A.Carrier = freydCaseArrow J M)
    (coherent : letI := readInstructions J M A h; RegionTypingCoherent (Φ := P.Instr) J M)
    (presentation : freydCaseAlgebra J M (readInstructions J M A h) = A) (e : CaseEquation P) :
    (ssaRoom J P).Sat (ShrinkHoms.toShrinkHoms (Discrete.mk (expandAlgebra J M A h coherent))) (reify e) ↔
      ((LetCase.inst Γ₀).obj P).Sat A e := by
  refine ((reifyCorridor J P).sat _ e).trans (Iff.of_eq ?_)
  exact congrArg (fun B => ((LetCase.inst Γ₀).obj P).Sat B e)
    (expandAlgebra_reduct A h coherent presentation)

/-- The corridor reflects equational consequence relative to the exact image
of its model reduct. -/
theorem entails_reify_iff_on_expansions (Γ : Set (CaseEquation P)) (e : CaseEquation P) :
    (ssaRoom J P).Entails (reify '' Γ) (reify e) ↔
      ∀ A : CaseAlgebra P, (∃ K : CoherentRegionModel J P, K.caseAlgebra = A) →
        (∀ φ ∈ Γ, ((LetCase.inst Γ₀).obj P).Sat A φ) → ((LetCase.inst Γ₀).obj P).Sat A e :=
  entails_reify_iff_on_expansions_proof Γ e

end Silmaril.Isotope.Institution.Acyclic

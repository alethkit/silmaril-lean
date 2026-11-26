module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Branch.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Branch.Trace

/-! # Reflection by testing both input tags in the concrete trace algebra -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch

open Sequence (Normal Sorts signature value run traceAlgebra traceJ traceTypes traceInstructions validatedTrace)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv)

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)

/-- The exact typed program has the predicted effect word and terminal
observation at each input constructor. -/
theorem ProgramBody.run_input (tail : List Sorts) (p : ProgramBody) (tag : value Input) :
    run (p.program tail).toLetCase.2 (boundEnv value (β := inputContext) (PUnit.unit, tag)) =
      (tag.elim (fun _ => p.normal.1) (fun _ => p.normal.2)).observe
        (Sum.inl PUnit.unit : value (packedExitType (Ty.unit :: tail))) :=
  run_program_proof tail p tag

theorem traceSat_iff_normal (tail : List Sorts) (p q : ProgramBody) :
    ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase (equation tail p q)) ↔
      p.normal = q.normal :=
  ⟨traceSat_normal_proof tail p q,
    fun h => Sequence.traceSat_of_repaired _ (repaired_of_normal tail p q h)⟩

theorem repaired_iff_normal (tail : List Sorts) (p q : ProgramBody) :
    Repaired false (equation tail p q) ↔ p.normal = q.normal :=
  ⟨fun h => traceSat_normal_proof tail p q (Sequence.traceSat_of_repaired _ h),
    repaired_of_normal tail p q⟩

theorem traceSat_iff_repaired (tail : List Sorts) (p q : ProgramBody) :
    ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase (equation tail p q)) ↔
      Repaired false (equation tail p q) :=
  (traceSat_iff_normal tail p q).trans (repaired_iff_normal tail p q).symm

/-- Room membership keeps the same region typing coherence premise as the
straight-line comparison. -/
theorem validatedTrace_sat_iff_repaired
    (coherent : letI := traceInstructions
      LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := signature.Instr) traceJ traceTypes)
    (tail : List Sorts) (p q : ProgramBody) :
    (grammarRoom traceJ signature).Sat (validatedTrace coherent) (equation tail p q) ↔
      Repaired false (equation tail p q) :=
  traceSat_iff_repaired tail p q

/-- The validated trace model is sufficient to reflect room-wide validity on
the branch slice whenever its region typing coherence is supplied. -/
theorem repaired_of_validated_valid
    (coherent : letI := traceInstructions
      LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := signature.Instr) traceJ traceTypes)
    (tail : List Sorts) (p q : ProgramBody)
    (valid : ∀ B : (grammarRoom traceJ signature).Mod,
      (grammarRoom traceJ signature).Sat B (equation tail p q)) :
    Repaired false (equation tail p q) :=
  (validatedTrace_sat_iff_repaired coherent tail p q).mp (valid (validatedTrace coherent))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch

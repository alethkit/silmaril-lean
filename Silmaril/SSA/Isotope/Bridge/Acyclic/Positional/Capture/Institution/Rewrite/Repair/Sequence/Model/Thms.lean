module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Trace

/-! # Reflection on ordered effect sequences -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)

/-- The concrete Freyd trace algebra observes the order of emits and the
identity of a terminating empty-producing operation. -/
theorem traceSat_iff_normal (tail : List Sorts) (p q : Body) :
    ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase (equation tail p q)) ↔
      p.normal = q.normal :=
  ⟨traceSat_normal_proof tail p q,
    fun h => traceSat_of_repaired_proof tail p q (sequencesEmpty_of_normal tail p q h).repaired⟩

/-- The normal form decides the full opt-in relation on this slice. The
forward implication tests all repaired derivations in the trace algebra. -/
theorem repaired_iff_normal (tail : List Sorts) (p q : Body) :
    Repaired false (equation tail p q) ↔ p.normal = q.normal :=
  ⟨fun h => (traceSat_iff_normal tail p q).mp (traceSat_of_repaired_proof tail p q h),
    fun h => (sequencesEmpty_of_normal tail p q h).repaired⟩

/-- Concrete satisfaction reflects back to the typed rewrite derivation
on these witnessed equations. -/
theorem traceSat_iff_repaired (tail : List Sorts) (p q : Body) :
    ((LetCase.inst Γ₀).obj signature).Sat traceAlgebra (grammarCase (equation tail p q)) ↔
      Repaired false (equation tail p q) :=
  (traceSat_iff_normal tail p q).trans (repaired_iff_normal tail p q).symm

/-- If the trace interpretation is region-typing-coherent, validity in its
validated room has the same characterization. -/
theorem validatedTrace_iff_repaired
    (coherent : letI := traceInstructions
      LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := signature.Instr)
        traceJ traceTypes)
    (tail : List Sorts) (p q : Body) :
    (∀ B : (grammarRoom traceJ signature).Mod, (grammarRoom traceJ signature).Sat B (equation tail p q)) ↔
      Repaired false (equation tail p q) :=
  ⟨fun h => (traceSat_iff_repaired tail p q).mp (h (validatedTrace coherent)),
    fun h => (sequencesEmpty_of_normal tail p q ((repaired_iff_normal tail p q).mp h)).sat⟩

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

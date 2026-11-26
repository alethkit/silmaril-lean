module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Normalize

/-! # Normalization by the typed empty-sequencing rule -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

/-- Matching traces give a derivation by the new rule under the actual entry
and operand binders. The selected exit and its ordered interface are preserved. -/
theorem sequencesEmpty_of_normal (tail : List Sorts) (p q : Body) (h : p.normal = q.normal) :
    SequencesEmpty (equation tail p q) :=
  sequencesEmpty_normal_proof tail p q h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

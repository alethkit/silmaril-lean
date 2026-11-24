module

public import Silmaril.ProofFormats.DaslSyntax.Database.Examples.Thms
public import Silmaril.Logic.HOLLight.Consistency

public section

namespace Silmaril.ProofFormats.DaslSyntax.Database.Examples.HOL

open Silmaril.Logic.HOLLight

/-- The closed fixture proposition holds in the specified standard model at every valuation. -/
theorem standardValidity : Valid Model.standard.{0} closed := by
  intro ρ ν
  exact closedProof.2.2.sound Model.standard (by simp [Models]) ρ ν (by simp [HypsTrue])

/-- The existing abstract name also resolves in the standard-model validity table. -/
theorem standardValidityRow : TermName.closed ∈ Database.HOL.validIn terms Model.standard.{0} :=
  Semantics.Naming.Lift.mem_where_iff.mpr ⟨closed, rfl, closedProof.2.2.typing, standardValidity⟩

end Silmaril.ProofFormats.DaslSyntax.Database.Examples.HOL

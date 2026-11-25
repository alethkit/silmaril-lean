module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Wiring.JumpResolution.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationJumpResolution

/-! # Termination of jump resolution -/

public section

universe w

namespace Silmaril.Calco2019.IterationTheory.Wiring

variable {σ : Signature.{w}} {I E : Arity} {g : Wiring σ I E}

/-- Contracting a jump to a distinct state strictly reduces the jump count. -/
theorem contract_decreases (s : g.states) (t : g.without s) (row : g.row s = .jump t.val) :
    (g.contract s t).jumpCount < g.jumpCount :=
  Proofs.IterationJumpResolution.contract_decreases s t row

/-- Replacing a self-jump by bottom strictly reduces the jump count. -/
theorem cut_decreases (s : g.states) (row : g.row s = .jump s) :
    (g.cut s).jumpCount < g.jumpCount :=
  Proofs.IterationJumpResolution.cut_decreases s row

/-- Every finite wiring has a sequence of jump resolutions ending at a ranked graph. -/
theorem exists_normalization (g : Wiring σ I E) : ∃ r, g.Normalizes r :=
  Proofs.IterationJumpResolution.exists_normalization g

end Silmaril.Calco2019.IterationTheory.Wiring

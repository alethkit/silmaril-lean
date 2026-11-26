module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.WellFormed.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Phi.WellFormed

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA

universe v w
variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]
variable {graph : Graph V K F} {inputs : List V} {cert : Certificate V K}

/-- Passing the certificate establishes global static uniqueness and earlier
availability for every read on every structural entry path. -/
theorem check_sound (checked : check graph inputs cert = true) : WellFormed graph inputs :=
  Proofs.SSA.LambdaRTL.CFG.CyclicPhi.GlobalSSA.check_sound checked

/-- The optional admission returns an existing lowering with an additional
source well-formedness guarantee. The source lowering and semantic theorems
can also be used directly with the original structural check. -/
theorem compile_sound {target : CFG (Option V × Nat) (Option K) F}
    (accepted : GlobalSSA.compile graph inputs cert = some target) :
    WellFormed graph inputs ∧ Phi.compile graph = some target :=
  Proofs.SSA.LambdaRTL.CFG.CyclicPhi.GlobalSSA.compile_sound accepted

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA

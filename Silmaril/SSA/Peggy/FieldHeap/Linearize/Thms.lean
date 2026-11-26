module

public import Silmaril.SSA.Peggy.FieldHeap.Linearize.Defs
import Silmaril.Proofs.SSA.Peggy.FieldHeap.Linearize.Sound

/-! # Correctness of straight-line field-heap reversion -/

public section

namespace Silmaril.SSA.Peggy.FieldHeap.Linearize

variable {params : List (PEG.Ty DataSort)} {reads nodes : Nat}
variable {g : Graph params reads nodes} {phase : Fin nodes → Nat}
variable {program : Program params reads nodes}

/-- An accepted graph has a well-founded Figure 11 demand relation. -/
theorem demandWellFounded (accepted : linearize g phase = .ok program) :
    WellFounded g.Demand := Proofs.demandWellFounded accepted

/-- Acceptance never discards an effect from the input table. -/
theorem effect_covered (accepted : linearize g phase = .ok program) (id : Fin nodes)
    (effectful : isEffect (g.node id) = true) : id ∈ program.schedule.effects :=
  Proofs.effect_covered accepted id effectful

/-- The schedule preserves the complete ordered Figure 11 observation,
including the final heap, first fault and every requested load value. -/
theorem run_eq_observe (accepted : linearize g phase = .ok program) (input : Inputs params)
    (i : PEG.Index 0) (wf : WellFounded g.Demand := demandWellFounded accepted) :
    program.run input = g.observe interpretation (g.denote interpretation input wf) i :=
  Proofs.run_eq_observe accepted input i wf

end Silmaril.SSA.Peggy.FieldHeap.Linearize

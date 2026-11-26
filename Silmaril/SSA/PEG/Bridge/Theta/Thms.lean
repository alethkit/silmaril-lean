module

public import Silmaril.SSA.PEG.Bridge.Theta.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
public import Silmaril.SSA.RVSDG.Theta.Categorical.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.PEG
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.RVSDG

public section

namespace Silmaril.SSA.PEG.Bridge.Theta

open RVSDG (Tuple)

variable {Data : Type} {P : InstructionSet.{0,0} Data} {a b : Ty Data}
variable (loop : Loop P a b) (m : TotalModel P)
variable (input : Tuple m.toPEG.Value [a, b])

/-- The finite checker covers every demand, including arbitrary sample indices. -/
theorem Loop.rank_check : rank.check loop.peg = true :=
  Proofs.rank_check loop

theorem Loop.demandWellFounded : WellFounded loop.peg.Demand :=
  loop.peg.demandWellFounded_of_check rank loop.rank_check

/-- Vertex five is the one shared pass. Its defined result is exactly the
least true test along the initialized state stream. -/
theorem Loop.pass_eq_some_iff (idx : Index 1) (k : Nat) (wf : WellFounded loop.peg.Demand) :
    loop.peg.denote m.toPEG input wf (5, idx) = some ⟨k⟩ ↔ loop.FirstExit m input k :=
  Proofs.pass_eq_some_iff loop m input wf idx k

/-- Both eval roots observe the input to the first stopping body activation,
with all preceding samples defined. -/
theorem Loop.observe_firstExit (idx : Index 1) (wf : WellFounded loop.peg.Demand)
    {k : Nat} (exit : loop.FirstExit m input k) :
    loop.peg.observe m.toPEG (loop.peg.denote m.toPEG input wf) idx =
      (loop.stateAt m k input).map (fun _ => some) :=
  Proofs.observe_firstExit loop m input wf idx exit

/-- The numbered body returns the exit/continue selector and the appropriate
tuple. The test reads the input to the current body activation. -/
theorem Loop.body_run :
    loop.toTheta.body.run (model m a b) (encodeCarried m input) =
      RVSDG.Theta.bodyResult (model m a b) (!(loop.exits m input))
        (encodeCarried m (if loop.exits m input then input else loop.advance m input)) :=
  Proofs.body_run loop m input

/-- The actual θ finite-return relation stops at exactly the PEG pass index. -/
theorem Loop.returns_iff_firstExit (output : Tuple m.toPEG.Value [a, b]) :
    loop.toTheta.Returns (model m a b) (encodeCarried m input) (encodeCarried m output) ↔
      ∃ k, loop.FirstExit m input k ∧ output = loop.stateAt m k input :=
  Proofs.returns_iff_firstExit loop m input output

/-- The compiled numbered graph has a finite return exactly when the guarded
PEG has the corresponding fully defined ordered observation. -/
theorem returns_iff_observe {g : Graph P [a, b] [a, b] 10 1} (form : Form g)
    (idx : Index 1) (wf : WellFounded g.Demand) (output : Tuple m.toPEG.Value [a, b]) :
    (compile form).Returns (model m a b) (encodeCarried m input) (encodeCarried m output) ↔
      g.observe m.toPEG (g.denote m.toPEG input wf) idx = output.map (fun _ => some) := by
  obtain ⟨loop, rfl⟩ := form
  exact (loop.returns_iff_firstExit m input output).trans (Proofs.observe_iff loop m input wf idx output).symm

/-- The existing RVSDG partial-value denotation gives the same finite observation. -/
theorem denotePart_eq_some_iff_observe {g : Graph P [a, b] [a, b] 10 1} (form : Form g)
    (idx : Index 1) (wf : WellFounded g.Demand) (output : Tuple m.toPEG.Value [a, b]) :
    (compile form).denotePart (model m a b) (encodeCarried m input) =
      Part.some (RVSDG.Categorical.pack (encodeCarried m output)) ↔
      g.observe m.toPEG (g.denote m.toPEG input wf) idx = output.map (fun _ => some) :=
  ((compile form).denotePart_eq_some (model m a b) (encodeCarried m input) (encodeCarried m output)).trans
    (returns_iff_observe m input form idx wf output)

end Silmaril.SSA.PEG.Bridge.Theta

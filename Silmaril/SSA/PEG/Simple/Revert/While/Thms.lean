module

public import Silmaril.SSA.PEG.Simple.Revert.While.Defs
public import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Correctness

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {state : Ty Data}
variable {g : Graph P [state] [state] 7 1}

/-- Recompiling the recovered loop gives the entire input graph. -/
theorem Certificate.compile_eq [DecidableEq Data] (cert : Certificate g) :
    cert.form.compile = g :=
  (Proofs.graph_eq cert).symm

theorem Certificate.demandWellFounded [DecidableEq Data] (cert : Certificate g) :
    WellFounded g.Demand :=
  cert.compile_eq ▸ cert.form.program.translate_demandWellFounded cert.form.negate

/-- A compiled canonical loop is admitted and extraction recovers its
source, including the three primitive symbols. -/
theorem Form.compile_extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (form : Form P state) : ∃ cert, extract form.compile = some cert ∧ cert.form = form :=
  Proofs.compile_extract form

/-- The successful returns of the extracted SIMPLE program are preserved by
the input PEG when the exposed negation opcode has its stated meaning. -/
theorem Certificate.observe_of_returns [DecidableEq Data] (cert : Certificate g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value [state]) {value : m.Value state}
    (notSem : ∀ b : Bool, m.run cert.form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (returns : cert.revert.Returns m input value) (idx : Index 1) :
    g.observe m (g.denote m input cert.demandWellFounded) idx = .cons (some value) .nil :=
  Proofs.observe_of_returns cert m input notSem returns idx cert.demandWellFounded

end Silmaril.SSA.PEG.Simple.Revert.While

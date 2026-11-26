module

public import Silmaril.SSA.PEG.Simple.Revert.While.Defs
public import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.SSA.PEG.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Proofs

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {state : Ty Data}
variable {g : Graph P [state] [state] 7 1}

theorem graph_eq [DecidableEq Data] (cert : Certificate g) : g = cert.form.compile :=
  Graph.eq_of_toRaw_eq cert.table

private theorem probe_compile [DecidableEq Data] (form : Form P state) :
    probe form.compile = some form := by
  change (do
    let negate ← castPrimitive form.negate [.bool] .bool
    let update ← castPrimitive form.update [state] state
    let guard ← castPrimitive form.guard [state] .bool
    pure ⟨guard, update, negate⟩) = some form
  simp [castPrimitive]

theorem compile_extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (form : Form P state) :
    ∃ cert, extract form.compile = some cert ∧ cert.form = form := by
  unfold extract
  rw [probe_compile]
  simp

theorem observe_of_returns [DecidableEq Data] (cert : Certificate g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value [state]) {value : m.Value state}
    (notSem : ∀ b : Bool, m.run cert.form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (returns : cert.revert.Returns m input value) (idx : Index 1)
    (wf : WellFounded g.Demand) :
    g.observe m (g.denote m input wf) idx = .cons (some value) .nil := by
  have e := graph_eq cert
  obtain ⟨form, _⟩ := cert
  change g = form.compile at e
  subst g
  exact form.program.translate_returns form.negate m input notSem returns idx

theorem returns_of_defined [DecidableEq Data] (cert : Certificate g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value [state]) (total : cert.form.program.Total m)
    (notSem : ∀ b : Bool, m.run cert.form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (wf : WellFounded g.Demand) (idx : Index 1) {value : m.Value state}
    (defined : g.observe m (g.denote m input wf) idx = .cons (some value) .nil) :
    cert.revert.Returns m input value := by
  have eq := graph_eq cert
  obtain ⟨form, _⟩ := cert
  change g = form.compile at eq
  subst g
  obtain ⟨_, final, witness⟩ := form.program.translate_exitWitness form.negate m input total
    notSem idx defined
  exact ⟨final, witness.trace.exec, witness.returned⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Proofs

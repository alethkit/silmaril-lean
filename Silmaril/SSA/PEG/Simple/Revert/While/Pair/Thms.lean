module

public import Silmaril.SSA.PEG.Simple.Revert.While.Pair.Defs
public import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Pair.Correctness

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Pair

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {left right result : Ty Data} {g : Graph P [left, right] [result] 10 1}

theorem Certificate.compile_eq [DecidableEq Data] (cert : Certificate g) :
    cert.form.compile = g :=
  Proofs.compile_eq cert

theorem Certificate.demandWellFounded [DecidableEq Data] (cert : Certificate g) :
    WellFounded g.Demand :=
  cert.compile_eq ▸ cert.form.program.translate_demandWellFounded cert.form.negate

/-- A successful bounded execution is a successful run of the emitted SIMPLE. -/
theorem Form.runFuel_returns (form : Form P left right result) (m : Interpretation.{u,v,w} P)
    (fuel : Nat) (input : Tuple m.Value [left, right]) {value : m.Value result}
    (success : form.runFuel m fuel input = some value) :
    form.program.source.Returns m input value :=
  Proofs.runFuel_returns form m fuel input success

/-- A defined PEG return gives a finite trace at the first pass index
and a defined eval prefix, under the complete-step totality contract. -/
theorem Certificate.exitWitness_of_defined [DecidableEq Data] (cert : Certificate g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value [left, right]) (total : cert.form.Total m)
    (notSem : ∀ b : Bool, m.run cert.form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {value : m.Value result}
    (defined : g.observe m (g.denote m input cert.demandWellFounded) idx = .cons (some value) .nil) :
    ∃ k final, cert.form.program.ExitWitness cert.form.negate m input
      (cert.form.compile.denote m input
        (cert.form.program.translate_demandWellFounded cert.form.negate)) idx k final value :=
  Proofs.exitWitness_of_defined m cert input total notSem cert.demandWellFounded idx defined

theorem Certificate.returns_of_defined [DecidableEq Data] (cert : Certificate g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value [left, right]) (total : cert.form.Total m)
    (notSem : ∀ b : Bool, m.run cert.form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {value : m.Value result}
    (defined : g.observe m (g.denote m input cert.demandWellFounded) idx = .cons (some value) .nil) :
    cert.revert.Returns m input value := by
  obtain ⟨_, final, h⟩ := cert.exitWitness_of_defined m input total notSem idx defined
  exact ⟨final, h.trace.exec, h.returned⟩

/-- The finite pass index is sufficient fuel to execute a defined return. -/
theorem Certificate.runFuel_of_defined [DecidableEq Data] (cert : Certificate g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value [left, right]) (total : cert.form.Total m)
    (notSem : ∀ b : Bool, m.run cert.form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {value : m.Value result}
    (defined : g.observe m (g.denote m input cert.demandWellFounded) idx = .cons (some value) .nil) :
    ∃ k, cert.form.runFuel m k input = some value ∧
      cert.form.program.readPort cert.form.negate m
        (cert.form.compile.denote m input
          (cert.form.program.translate_demandWellFounded cert.form.negate))
        cert.form.program.passPort idx = some ⟨k⟩ := by
  obtain ⟨k, _, h⟩ := cert.exitWitness_of_defined m input total notSem idx defined
  exact ⟨k, (Proofs.runFuel_of_trace cert.form m total h.trace).trans (congrArg some h.returned), h.pass⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Pair

module

public import Silmaril.SSA.PEG.Simple.Revert.While.Pair.Defs
public import Silmaril.SSA.PEG.Simple.While.Thms
public import Silmaril.SSA.PEG.Simple.Thms
import Silmaril.SSA.PEG.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Pair.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {left right result : Ty Data}
variable {g : Graph P [left, right] [result] 10 1}

theorem compile_eq [DecidableEq Data] (cert : Certificate g) : cert.form.compile = g :=
  (Graph.eq_of_toRaw_eq cert.table).symm

variable (form : Form P left right result) (m : Interpretation.{u,v,w} P)

theorem step_exec {store next : Tuple m.Value [left, right]}
    (success : form.step m store = some next) :
    Exec m form.program.body.enableWhile store (some next) := by
  cases hl : m.run form.leftStep (.cons (store.get .head) .nil) with
  | none => simp [Form.step, hl] at success
  | some x =>
    cases hr : m.run form.rightStep store with
    | none => simp [Form.step, hl, hr] at success
    | some y =>
      have assigned : (Tuple.cons x (.cons y .nil) : Tuple m.Value [left, right]) = next :=
        Option.some.inj (by simpa [Form.step, hl, hr] using success)
      subst next
      have same : Tuple.cons (store.get .head) (.cons (store.get (.tail .head)) .nil) = store := by
        cases store with | cons x tail =>
        cases tail with | cons y tail =>
        cases tail
        rfl
      let withLeft : Tuple m.Value (left :: left :: right :: []) := .cons x store
      let withBoth : Tuple m.Value (right :: left :: left :: right :: []) := .cons y withLeft
      refine .seq (next := withLeft) (.assign hl)
        (.seq (next := withBoth) (.assign ?_) .project)
      change m.run form.rightStep
        (.cons (store.get .head) (.cons (store.get (.tail .head)) .nil)) = some y
      rw [same]
      exact hr

private theorem step_total (total : form.Total m) (store : Tuple m.Value [left, right]) :
    ∃ next, form.step m store = some next := by
  obtain ⟨x, hx⟩ := total.leftStep (store.get .head)
  obtain ⟨y, hy⟩ := total.rightStep store
  exact ⟨.cons x (.cons y .nil), by simp [Form.step, hx, hy]⟩

theorem programTotal (total : form.Total m) : form.program.Total m where
  guard store := total.guard (store.get .head)
  body store := by
    obtain ⟨next, ran⟩ := step_total form m total store
    exact ⟨next, step_exec form m ran⟩

theorem runFuel_of_trace (total : form.Total m) {k : Nat}
    {input final : Tuple m.Value [left, right]}
    (trace : WhileTrace m form.program.guard form.program.body.enableWhile k input final) :
    form.runFuel m k input = some (final.get form.retvar) := by
  induction trace with
  | stop test =>
    rw [Form.runFuel.eq_def]
    simp [test]
  | @step k start next final test body _ ih =>
    obtain ⟨computed, ran⟩ := step_total form m total start
    have same := Option.some.inj (Exec.deterministic (step_exec form m ran) body)
    subst computed
    rw [Form.runFuel.eq_def]
    simpa [test, ran] using ih

theorem runFuel_returns (fuel : Nat) (input : Tuple m.Value [left, right]) {value : m.Value result}
    (success : form.runFuel m fuel input = some value) :
    form.program.source.Returns m input value := by
  rw [Form.runFuel.eq_def] at success
  cases test : form.program.guard.eval m input with
  | none => simp [test] at success
  | some flag =>
    rcases flag with ⟨flag⟩
    cases flag
    · have h : some (input.get form.retvar) = some value := by simpa [test] using success
      exact ⟨input, .whileStop test, Option.some.inj h⟩
    · cases fuel with
      | zero => simp [test] at success
      | succ fuel =>
        cases step : form.step m input with
        | none => simp [test, step] at success
        | some next =>
          have returned : form.runFuel m fuel next = some value := by
            simpa [test, step] using success
          obtain ⟨final, ran, returned⟩ := runFuel_returns fuel next returned
          exact ⟨final, .whileStep test (step_exec form m step) ran, returned⟩
termination_by fuel

theorem exitWitness_of_defined [DecidableEq Data] (cert : Certificate g)
    (input : Tuple m.Value [left, right]) (total : cert.form.Total m)
    (notSem : ∀ b : Bool, m.run cert.form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (wf : WellFounded g.Demand) (idx : Index 1) {value : m.Value result}
    (defined : g.observe m (g.denote m input wf) idx = .cons (some value) .nil) :
    ∃ k final, cert.form.program.ExitWitness cert.form.negate m input
      (cert.form.compile.denote m input
        (cert.form.program.translate_demandWellFounded cert.form.negate)) idx k final value := by
  have eq := compile_eq cert
  obtain ⟨form, _⟩ := cert
  change form.compile = g at eq
  subst g
  exact form.program.translate_exitWitness form.negate m input (programTotal form m total)
    notSem idx defined

end Silmaril.SSA.PEG.Simple.Revert.While.Pair.Proofs

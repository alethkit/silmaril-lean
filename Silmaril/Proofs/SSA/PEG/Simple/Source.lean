module

public import Silmaril.SSA.PEG.Simple.Defs

public section

namespace Silmaril.SSA.PEG.Simple.Proofs

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {model : Interpretation.{u,v,w} P}

private theorem liftedBool_inj {b c : Bool}
    (h : some (ULift.up b : ULift.{w} Bool) = some (ULift.up c)) : b = c :=
  congrArg ULift.down (Option.some.inj h)

theorem deterministic {loops : Bool} {vars outs : List (Ty Data)}
    {s : Stmt P loops vars outs} {store : Tuple model.Value vars}
    {a b : Option (Tuple model.Value outs)}
    (first : Exec model s store a) (second : Exec model s store b) : a = b := by
  induction first with
  | assign h => cases second <;> simp_all
  | assignFailed h => cases second <;> simp_all
  | project =>
    cases second
    rfl
  | firstFailed a ih =>
    cases second with
    | firstFailed => rfl
    | seq second _ => cases ih second
  | seq a _ iha ihb =>
    cases second with
    | firstFailed second => cases iha second
    | seq second rest =>
      have e := Option.some.inj (iha second)
      subst e
      exact ihb rest
  | branchFailed h => cases second <;> simp_all
  | branchTrue h _ ih =>
    cases second <;> first | exact ih ‹_› | simp_all
    have := liftedBool_inj ‹_›
    contradiction
  | branchFalse h _ ih =>
    cases second <;> first | exact ih ‹_› | simp_all
    have := liftedBool_inj ‹_›
    contradiction
  | whileGuardFailed h => cases second <;> simp_all
  | whileStop h => cases second <;> simp_all <;> (have := liftedBool_inj ‹_›; contradiction)
  | whileBodyFailed h first ih =>
    cases second with
    | whileGuardFailed => simp_all
    | whileStop =>
      simp_all
      have := liftedBool_inj ‹_›
      contradiction
    | whileBodyFailed => rfl
    | whileStep _ second _ => cases ih second
  | whileStep h _ _ ihstep ihrest =>
    cases second with
    | whileGuardFailed => simp_all
    | whileStop =>
      simp_all
      have := liftedBool_inj ‹_›
      contradiction
    | whileBodyFailed _ second => cases ihstep second
    | whileStep _ second rest =>
      have e := Option.some.inj (ihstep second)
      subst e
      exact ihrest rest

theorem runLoopFree_exec {vars outs : List (Ty Data)} (s : Stmt P false vars outs)
    (store : Tuple model.Value vars) : Exec model s store (s.runLoopFree model store) :=
  match s with
  | .assign rhs => by
    rw [Stmt.runLoopFree]
    cases h : rhs.eval model store with
    | none => exact .assignFailed h
    | some value => exact .assign h
  | .project _ => .project
  | .seq first second => by
    rw [Stmt.runLoopFree]
    have run := runLoopFree_exec first store
    cases h : first.runLoopFree model store with
    | none => exact .firstFailed (h ▸ run)
    | some next => exact .seq (h ▸ run) (runLoopFree_exec second next)
  | .branch guard yes no => by
    rw [Stmt.runLoopFree]
    cases h : guard.eval model store with
    | none => exact .branchFailed h
    | some flag =>
      rcases flag with ⟨flag⟩
      cases flag
      · exact .branchFalse h (runLoopFree_exec no store)
      · exact .branchTrue h (runLoopFree_exec yes store)
  | .while impossible _ _ => nomatch impossible
termination_by structural s

theorem runLoopFree_of_returns {vars : List (Ty Data)} {t : Ty Data}
    {p : Program P false vars t} {input : Tuple model.Value vars} {value : model.Value t}
    (h : p.Returns model input value) : p.runLoopFree model input = some value := by
  obtain ⟨final, exec, ret⟩ := h
  unfold Program.runLoopFree
  rw [deterministic (runLoopFree_exec p.body input) exec]
  exact congrArg some ret

end Silmaril.SSA.PEG.Simple.Proofs

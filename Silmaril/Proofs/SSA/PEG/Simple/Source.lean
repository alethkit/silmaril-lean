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

end Silmaril.SSA.PEG.Simple.Proofs

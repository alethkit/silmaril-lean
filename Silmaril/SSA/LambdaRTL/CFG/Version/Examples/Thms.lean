module

public import Silmaril.SSA.LambdaRTL.CFG.Version.Thms

/-! A live-in crossing a join needs the pair law. The CFG checker guards label
identity independently of the semantic model. -/

@[expose] public section
namespace Silmaril.SSA.LambdaRTL.CFG.VersionExamples

private inductive Value where
  | word (value : Nat)
  | pair (left right : Value)
  deriving DecidableEq

private def model : Model Empty Option Value where
  unit := .word 0
  pair := .pair
  inl := id
  inr := id
  unpair
    | .pair a b => some (a, b)
    | _ => none
  split _ := none
  app op _ := op.elim
  abort _ := none

private def badPair : Model Empty Option Value := { model with unpair := fun _ => none }

private theorem pairLaw : model.PairLawful := ⟨fun _ _ => rfl⟩

-- The jump-site assignment changes the live-in `true` seen by the handler.
private def source : Region Bool Nat Empty :=
  .join (.let1 true (.val (.var false)) (.br 10 (.var false))) 10 false (.br 99 (.var true))

private def input (reg : Bool) : Value := if reg then .word 7 else .word 3
private def versionInput (reg : Bool × Nat) : Value := input reg.1

private def exit (label : Nat) : Nat := label + 100

private def label : Nat ⊕ Path → Nat
  | .inl x => exit x
  | .inr _ => 1

private def candidate : CFG (Bool × Nat) Nat Empty :=
  (flatten (Version.versionTop source)).relabel label

private theorem accepted : validate exit (Version.versionTop source) candidate = true := by decide

example : obs <$> candidate.run model versionInput = some (199, .word 3) := by
  rw [validate_versionTop_obs model pairLaw exit source candidate accepted]
  decide

example : source.evalSSA model input = some (99, .word 7) := by decide
example : source.evalObs model input = some (99, .word 3) := by decide

-- Checking shape alone cannot supply the model law used to unpack the live-in.
example : ¬ badPair.PairLawful := by
  intro law
  nomatch law.unpair_pair (.word 0) (.word 0)

example : source.evalObs badPair input = some (99, .word 3) := by decide
example : obs <$> candidate.run badPair versionInput = none := by decide

-- This candidate agrees with the requested renaming, but the internal block
-- and visible exit both map to label 1, so the validator refuses it.
example : validate (fun _ => 1) (Version.versionTop source)
    ((flatten (Version.versionTop source)).relabel fun _ => 1) = false := by decide

end Silmaril.SSA.LambdaRTL.CFG.VersionExamples

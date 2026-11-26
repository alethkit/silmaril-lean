module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Defs
public import Silmaril.Logic.Institution.Observational.Sentence
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Satisfaction

/-! Satisfaction for finite return observations in the concrete word model. -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution

open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy model)
open Silmaril.SSA.SeaOfNodes
open Silmaril.Logic.Institution.Observational (Sentence)

variable {arity : Nat} {entrySigs sigs rightEntry rightSigs : List (List PortTy)}
variable {left : SourceWithEntry arity entrySigs sigs} {right : SourceWithEntry arity rightEntry rightSigs}
variable {leftTargets rightTargets : Checked.Phi.Targets}

/-- The room's return projection is the existing guarded-row λSSA observation. -/
theorem lambdaReturns_eq (input : WordTuple arity) (initial : Memory) (region : LambdaScope arity) :
    lambdaReturns input initial region = Rows.lambdaObservation region.val input initial :=
  Proofs.lambdaReturns_eq input initial region

/-- The target return sets contain exactly their native partial observation with full memory. -/
theorem observations_eq (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) :
    Rows.rtlObservation leftTargets.1 input initial = {result | result ∈ nativeDenote left input initial} ∧
      lambdaReturns input initial (scope accepted) = {result | result ∈ nativeDenote left input initial} :=
  Proofs.observations_eq accepted input initial

/-- At a shared input and initial memory, both emitted observation equations
and the cross-backend comparison reflect native partial equality. -/
theorem equation_at_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets)
    (input : WordTuple arity) (initial : Memory) :
    let native := left.denote model input = right.denote model input
    ((Sentence.eq leftTargets.1 rightTargets.1).Holds (fun target => Rows.rtlObservation target input initial)
        ↔ native) ∧
      ((Sentence.eq (scope leftChecked) (scope rightChecked)).Holds (lambdaReturns input initial) ↔ native) ∧
      (Rows.rtlObservation leftTargets.1 input initial = lambdaReturns input initial (scope rightChecked) ↔ native) :=
  Proofs.equation_at_iff leftChecked rightChecked input initial

/-- Native equation satisfaction is exactly satisfaction of each emitted
return-observation equation at all typed inputs, for any fixed initial memory. -/
theorem equation_holds_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets) (initial : Memory) :
    let native := (Loop.Institution.Sentence.equation (equation left right)).Holds model
    ((∀ input : WordTuple arity, (Sentence.eq leftTargets.1 rightTargets.1).Holds
        (fun target => Rows.rtlObservation target input initial)) ↔ native) ∧
      ((∀ input : WordTuple arity, (Sentence.eq (scope leftChecked) (scope rightChecked)).Holds
        (lambdaReturns input initial)) ↔ native) ∧
      ((∀ input : WordTuple arity, Rows.rtlObservation leftTargets.1 input initial =
        lambdaReturns input initial (scope rightChecked)) ↔ native) :=
  Proofs.equation_holds_iff leftChecked rightChecked initial

/-- The native termination sentence holds exactly when each typed input
has a finite return on the corresponding emitted target. -/
theorem terminates_holds_iff (accepted : lowerChecked left = some leftTargets) (initial : Memory) :
    let native := (Loop.Institution.Sentence.terminates (program left)).Holds model
    ((∀ input : WordTuple arity, (Rows.rtlObservation leftTargets.1 input initial).Nonempty) ↔ native) ∧
      ((∀ input : WordTuple arity, (lambdaReturns input initial (scope accepted)).Nonempty) ↔ native) :=
  Proofs.terminates_holds_iff accepted initial

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution

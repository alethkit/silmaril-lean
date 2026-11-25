module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Defs

/-! # Typed fixture for native LambdaSSA fixpoint sequencing -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.SequencingObstruction

open Silmaril.DeBruijn (lift)

inductive Instruction where
  | tick

instance : HasTy Instruction (Ty Empty) where
  src _ := .unit
  trg _ := .unit

/-- Three states in order, encoded by the injections of a nested sum. -/
def stateType : Ty Empty := .coprod .unit (.coprod .unit .unit)

/-- Evaluate a unit instruction on each step. The first two states request
another iteration with the successor state, and the third returns unit. -/
def producer : Region Instruction :=
  .let₁ (.op .tick .unit)
    (.case (.var 1)
      (.br 0 (.inr (.inr (.inl .unit))))
      (.case (.var 0)
        (.br 0 (.inr (.inr (.inr .unit))))
        (.br 0 (.inl .unit))))

/-- Enter the step directly under the original feedback binder. -/
def unfolded : Region Instruction :=
  .cfg (SyntacticCategory.iterationBody producer) 1
    (fun _ => (SyntacticCategory.iterationBody producer).renameVars (lift Nat.succ))

/-- Place the feedback binder inside the continuation applied to the producer. -/
def sequenced : Region Instruction :=
  producer.lsubst (fun _ => .cfg SyntacticCategory.iterationDispatch 1
    (fun _ => ((SyntacticCategory.iterationBody producer).renameVars (lift Nat.succ)).renameVars
      (lift Nat.succ)))

/-- The fixpoint equation's composition with a continuation that returns or
starts the same loop. The repeat arm ignores the sum slot and old state. -/
def returnOrRepeat : Region Instruction :=
  .case (.var 0) (.br 0 (.var 0))
    ((SyntacticCategory.iterateRegion stateType producer).renameVars (lift (Nat.succ ∘ Nat.succ)))

end Silmaril.Isotope.LambdaSSA.Region.SequencingObstruction

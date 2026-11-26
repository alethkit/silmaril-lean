module

import Silmaril.SSA.SeaOfNodes.GCM.Sink.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink.Regression

open Silmaril.SSA.SeaOfNodes.GCM.Sink
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private inductive Op where
  | increment

private instance : HasTy Op (Ty Unit) where
  src _ := .base ()
  trg _ := .base ()

private def original : Region Op :=
  .cfg (.let₁ (.op .increment (.var 1)) (.case (.var 1) (.br 0 (.var 1)) (.br 1 (.var 4))))
    2 (fun _ => .br 2 (.var 0))

private theorem accepted : sink? original = some (after .increment) := rfl

private def leadingOp? : Region Op → Option Op
  | .let₁ (.op op _) _ => some op
  | _ => none

private def blockOps : Region Op → Option Op × List (Option Op)
  | .cfg entry _ blocks => (leadingOp? entry, List.ofFn fun i => leadingOp? (blocks i))
  | _ => (none, [])

example : blockOps original = (some .increment, [none, none]) := rfl
example : (sink? original).map blockOps = some (none, [some .increment, none]) := rfl

-- The right branch may not read the entry let's result.
private def usedTwice : Region Op :=
  .cfg (.let₁ (.op .increment (.var 1)) (.case (.var 1) (.br 0 (.var 1)) (.br 1 (.var 1))))
    2 (fun _ => .br 2 (.var 0))

example : sink? usedTwice = none := rfl

example : (after Op.increment).HasType (inputs (τ := Ty Unit) Op.increment) [.base ()] :=
  after_hasType Op.increment

private def compute : Op → Value Nat → Value Nat
  | .increment, .atom n => .atom (n + 1)
  | .increment, value => value

private def env (tag operand fallback : Value Nat) : Env Nat
  | 0 => tag
  | 1 => operand
  | 2 => fallback
  | _ => .unit

example : Eval (instruction compute) (env (.inl .unit) (.atom 5) (.atom 99))
    original (17 : Nat) 0 (.atom 6) 17 :=
  (sink?_eval_iff accepted compute _ _ _ _ _).mpr
    ((after_eval_iff compute .increment _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)

example : Eval (instruction compute) (env (.inr .unit) (.atom 5) (.atom 99))
    (after .increment) (17 : Nat) 0 (.atom 99) 17 :=
  (after_eval_iff compute .increment _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩

example : Eval (instruction compute) (env (.inr .unit) (.atom 11) (.atom 99))
    original (17 : Nat) 0 (.atom 99) 17 :=
  (sink?_eval_iff accepted compute _ _ _ _ _).mpr
    ((after_eval_iff compute .increment _ _ _ _ _).mpr ⟨rfl, rfl, rfl⟩)

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink.Regression

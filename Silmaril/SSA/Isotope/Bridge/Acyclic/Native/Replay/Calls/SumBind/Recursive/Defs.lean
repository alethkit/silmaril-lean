module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Continuation.Defs

/-! # The recursive operand fragment of outward call replay -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Recursive

/-- Calls, unary lets, ordered pairs, and cases can recur in every operand.
Variables, unit, and constructor-only injections are the remaining forms. -/
def Admitted {Φ : Type*} : Tm Φ → Prop
  | .op _ a => Admitted a
  | .let₁ a b | .pair a b => Admitted a ∧ Admitted b
  | .case e l r => Admitted e ∧ Admitted l ∧ Admitted r
  | a => ConstructorOnly a

/-- Concatenate the request words of a producing schedule and its continuation.
The output label comes from the continuation. Specializing a known tag can
delete paths from this list. -/
def appendPaths {Φ : Type*} (before after : List (List Φ × Nat)) : List (List Φ × Nat) :=
  before.flatMap fun p => after.map fun q => (p.1 ++ q.1, q.2)

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.SumBind.Recursive

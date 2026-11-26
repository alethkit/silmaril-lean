module

import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

/-! A γ either bypasses a θ or enters it. The loop carries a natural number
and a Boolean, and the enclosing region yields the two in reverse order. -/

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Examples

open NestedTheta.Institution
open OrderedRuntime.Structured (Data Values)

private abbrev carry : Ports (PortSort Bool) := [.value false, .value true]
private abbrev tagged : Ports (PortSort Bool) := .control 2 :: carry
private abbrev result : Ports (PortSort Bool) := [.value true, .value false]

private abbrev carryData : Data carry := .value (.value .nil)
private abbrev taggedData : Data tagged := .control carryData
private abbrev resultData : Data result := .value (.value .nil)

private inductive Opcode : Dialect Bool PUnit where
  | count : Opcode carry tagged
  | spin : Opcode carry tagged

private abbrev source : Stateless.Signature Bool := ⟨Opcode, fun op => by
  cases op <;> exact ⟨carryData, taggedData⟩⟩

private abbrev value : Bool → Type
  | false => Nat
  | true => Bool

private def state (n : Nat) (b : Bool) : Tuple (Values value) carry := .cons n (.cons b .nil)
private def input (arm : Fin 2) : Tuple (Values value) tagged := .cons ⟨arm⟩ (state 0 true)
private def output (b : Bool) (n : Nat) : Tuple (Values value) result := .cons b (.cons n .nil)

private def model : Stateless.Model source where
  value := value
  run
    | .count, .cons n (.cons b .nil) =>
      if (show Nat from n) < 2 then .cons ⟨1⟩ (state (Nat.succ n) (!b))
      else .cons ⟨0⟩ (state (Nat.add n 10) (!b))
    | .spin, x => .cons ⟨1⟩ x

private def argWires {past : List (Ports (PortSort Bool))} (ports : Ports (PortSort Bool)) : Wires ports past ports :=
  (NestedTheta.identityPorts ports).map fun _ => .arg

private def opResults {params : Ports (PortSort Bool)} (ports : Ports (PortSort Bool)) :
    Wires params [ports] ports :=
  (NestedTheta.identityPorts ports).map fun _ => Origin.output (past := [ports]) (0 : Fin 1)

private def body (op : Opcode carry tagged) : NestedTheta.Term source.op carry [] [tagged] tagged :=
  .bind ⟨carry, .base (.simple (.pure op)), argWires carry, Fin.elim0⟩
    (fun i => i.elim0) (.ret (opResults tagged))

private def loop (op : Opcode carry tagged) (discard : Bool) :
    NestedTheta.Term source.op carry [] [carry] carry :=
  .bind (NestedTheta.thetaVertex [tagged]) (fun _ => body op)
    (.ret (if discard then argWires carry else opResults carry))

private def branch : NestedTheta.Node source.op tagged [] carry :=
  ⟨tagged, .base (.gamma 0), argWires tagged, Fin.cases [] (fun _ => [carry])⟩

private def program (op : Opcode carry tagged) (discard : Bool) :
    NestedTheta.Term source.op tagged [] [carry] result :=
  .bind branch (Fin.cases
    (motive := fun i => NestedTheta.Term source.op carry [] (branch.childSigs i) carry)
    (.ret (argWires carry)) (fun _ => loop op discard))
    (.ret (.cons (.output (0 : Fin 1) (.tail .head)) (.cons (.output (0 : Fin 1) .head) .nil)))

private theorem loop_stateFree (op : Opcode carry tagged) (discard : Bool) : Stateless.NoState (loop op discard) :=
  ⟨carryData, carryData, fun _ => ⟨carryData, taggedData, fun i => i.elim0, carryData, taggedData⟩,
    carryData, carryData⟩

private theorem program_stateFree (op : Opcode carry tagged) (discard : Bool) :
    Stateless.NoState (program op discard) := by
  refine ⟨taggedData, carryData, ?_, taggedData, resultData⟩
  intro i
  refine Fin.cases (motive := fun i => Stateless.NoState (Fin.cases
    (motive := fun j => NestedTheta.Term source.op carry [] (branch.childSigs j) carry)
    (.ret (argWires carry)) (fun _ => loop op discard) i)) ?_ ?_ i
  · exact ⟨carryData, carryData⟩
  · exact fun _ => loop_stateFree op discard

private def compiled (op : Opcode carry tagged) (discard : Bool) : Region source tagged result :=
  lower (program op discard).toGraph (by
    rw [NestedTheta.Term.toTerm_toGraph]
    exact program_stateFree op discard)

private theorem compiled_eq (op : Opcode carry tagged) (discard : Bool) :
    compiled op discard = lowerTerm (program op discard) := by
  simp only [compiled, lower, NestedTheta.Term.toTerm_toGraph]

/-- The bypass arm immediately yields its arguments, even with a spinning
feedback operation in the other arm. -/
theorem bypass_returns : (compiled .spin true).Returns model (input 0) (output true 0) := by
  rw [compiled_eq]
  exact ⟨state 0 true, rfl, rfl⟩

/-- The chosen θ completes two restarts before the exit updates the carry once
more. The enclosing region returns the Boolean first and the number second. -/
theorem finite_feedback_returns : (compiled .count false).Returns model (input 1) (output false 12) := by
  rw [compiled_eq]
  refine ⟨state 12 false, ⟨state 12 false, ⟨state 2 true, ?_, rfl⟩, rfl⟩, rfl⟩
  exact (Relation.ReflTransGen.single (b := state 1 false) (by rfl)).tail (by rfl)

/-- An actual infinite path for the body of the spin arm, with a completed
activation at every transition. -/
theorem spin_productive : Productive (lowerTerm (body .spin)) model (state 0 true) :=
  ⟨fun _ => state 0 true, rfl, fun _ => rfl⟩

/-- The spinning arm prevents a finite return even though the continuation
would discard every feedback result. -/
theorem spin_no_return (returned : Tuple (Values value) result) :
    ¬ (compiled .spin true).Returns model (input 1) returned := by
  rw [compiled_eq]
  rintro ⟨_, ⟨_, ⟨last, _, exit⟩, _⟩, _⟩
  obtain ⟨n, ⟨b, ⟨⟩⟩⟩ := last
  cases exit

end Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Examples

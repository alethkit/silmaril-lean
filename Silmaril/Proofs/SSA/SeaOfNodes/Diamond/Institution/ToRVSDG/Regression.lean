module

import Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG

open CategoryTheory
open RVSDG (Port Tuple)

set_option backward.isDefEq.respectTransparency false

private abbrev word : ValueSort Unit := .data ()
private abbrev inputs : List (ValueSort Unit) := [.predicate, word]
private abbrev sigs : List (List (Ty Unit)) := [[.value word], [.value word]]

private inductive Arithmetic : Diamond.Signature.{0, 0} Unit
  | inc : Arithmetic [word] word
  | double : Arithmetic [word] word

private abbrev sig : Signature.{0, 0} Unit := ⟨Arithmetic⟩

private def arithmetic : Model.{0, 0, 0} sig.op where
  value _ := Nat
  run
    | .inc, .cons n .nil => Nat.succ n
    | .double, .cons n .nil => Nat.add n n

private def swap : sig ⟶ sig :=
  ⟨fun
    | .inc => .double
    | .double => .inc⟩

private def diamond (onTrue onFalse : Arithmetic [word] word) : Graph sig.op inputs sigs word where
  dataflow :=
    .cons onTrue (.cons (.arg (.tail .head)) .nil)
      (.cons onFalse (.cons (.arg (.tail .head)) .nil) .nil)
  predicate := .arg .head
  phi := ⟨⟨.onFalse⟩, fun
    | .first => .output (1 : Fin 2) .head
    | .second => .output (0 : Fin 2) .head⟩

private def entry (pred : Bool) : Tuple (Val arithmetic.value) (dataPorts inputs) :=
  .cons ⟨pred⟩ (.cons (4 : Nat) .nil)

private def sentence : Equation sig :=
  ⟨inputs, word, sigs, sigs, diamond .inc .double, diamond .double .double⟩

private abbrev target := RVSDG.Institution.inst.{0, 0, 0} (ValueSort Unit) PEmpty
private abbrev source := Institution.inst.{0, 0, 0} Unit
private abbrev lift := signatureFunctor.{0, 0} Unit

-- The first Region predecessor is the false arm. The primitive swap still
-- flips the results at the actual γ outputs while preserving both arm labels.
example : (RVSDG.Institution.mapGraph (mapOpcode swap) sentence.lhs.lower).run
    arithmetic.toRVSDG (entry true) = .cons (8 : Nat) .nil := by
  rw [Graph.lower, RVSDG.Institution.mapGraph_toGraph, RVSDG.Term.run_toGraph]
  rfl

example : (RVSDG.Institution.mapGraph (mapOpcode swap) sentence.lhs.lower).run
    arithmetic.toRVSDG (entry false) = .cons (5 : Nat) .nil := by
  rw [Graph.lower, RVSDG.Institution.mapGraph_toGraph, RVSDG.Term.run_toGraph]
  rfl

example : (target.I.map (lift.map swap)).sen (lowerEquation sentence) =
    lowerEquation ((source.I.map swap).sen sentence) :=
  lowerEquation_map swap sentence

example : ((target.I.map (lift.map swap)).mod.obj (Discrete.mk arithmetic.toRVSDG)).as =
    ((source.I.map swap).mod.obj (Discrete.mk arithmetic)).as.toRVSDG :=
  model_reduct swap arithmetic

example : (target.I.obj (lift.obj sig)).Sat (Discrete.mk arithmetic.toRVSDG)
    ((target.I.map (lift.map swap)).sen (lowerEquation sentence)) ↔
    (source.I.obj sig).Sat ((source.I.map swap).mod.obj (Discrete.mk arithmetic)) sentence :=
  satisfaction_map swap sentence arithmetic

-- The same carriers and user primitives admit a different dispatch in the
-- full RVSDG room. An always-false selector erases this equation's difference.
private def alwaysFalse : RVSDG.Model (signature sig).op where
  value := arithmetic.toRVSDG.value
  state := arithmetic.toRVSDG.state
  run
    | .pure op, input => arithmetic.toRVSDG.run (.pure op) input
    | .dispatch _, .cons _ captures => .cons ⟨1⟩ captures

private abbrev choices : List (ValueSort Unit) := [.predicate, word, word]

private def choose (onTrue : Port (dataPorts choices) (.value word)) :
    Graph sig.op choices [] word :=
  ⟨.nil, .arg .head, ⟨⟨.onFalse⟩, fun
    | .first => .arg (.tail (.tail .head))
    | .second => .arg onTrue⟩⟩

private def dispatchWitness : Equation sig :=
  ⟨choices, word, [], [], choose (.tail .head), choose (.tail (.tail .head))⟩

private theorem falseDispatch_agrees (flag : ULift Bool) (first second : Nat) :
    let input : Tuple alwaysFalse.Val (dataPorts choices) := .cons flag (.cons first (.cons second .nil))
    dispatchWitness.lhs.lower.run alwaysFalse input = dispatchWitness.rhs.lower.run alwaysFalse input := by
  simp only [Graph.lower, RVSDG.Term.run_toGraph]
  rfl

example : (lowerEquation dispatchWitness).Holds alwaysFalse := fun
  | .cons flag (.cons first (.cons second .nil)) => falseDispatch_agrees flag first second

example : ¬ dispatchWitness.Holds arithmetic := by
  intro holds
  have different := holds (.cons ⟨true⟩ (.cons (0 : Nat) (.cons (1 : Nat) .nil)))
  change (0 : Nat) = 1 at different
  cases different

end Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG

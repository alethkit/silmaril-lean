module

import Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Thms
import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Tests

open CategoryTheory Silmaril.Logic.Institution
open OrderedRuntime.Structured (Ty Values)
open OrderedState.Partial (Abnormal Block Restart abnormal abnormalAt observe runOpen)

private abbrev dataPorts : Ports (Ty Unit) := [.value ()]
private abbrev bodyPorts : Ports (Ty Unit) := Theta.BodyResults dataPorts
private abbrev args : Ports (Ty Unit) := .control 2 :: dataPorts
private abbrev NoPure : Dialect Unit Unit := fun _ _ => Empty

private inductive SourceEffect : Dialect Unit Unit where
  | guarded : SourceEffect dataPorts bodyPorts
  | restart : SourceEffect dataPorts bodyPorts

private inductive TargetEffect : Dialect Unit Unit where
  | tryTick : TargetEffect dataPorts bodyPorts
  | tick : TargetEffect dataPorts bodyPorts

private abbrev source : Signature Unit := ⟨⟨NoPure, SourceEffect⟩⟩
private abbrev target : Signature Unit := ⟨⟨NoPure, TargetEffect⟩⟩

private def effectMap : RVSDG.Institution.OpcodeMap SourceEffect TargetEffect
  | _, _, .guarded => .tryTick
  | _, _, .restart => .tick

private def migrate : source ⟶ target where
  forget := ⟨(fun op => nomatch op), effectMap⟩
  effect_injective _ _ := by
    intro a b eq
    cases a <;> cases b
    · rfl
    · cases eq
    · cases eq
    · rfl

private def body (op : SourceEffect dataPorts bodyPorts) :
    Term source.base.op dataPorts [] [bodyPorts] bodyPorts :=
  let node : Node source.base.op dataPorts [] bodyPorts :=
    ⟨dataPorts, .base (.simple (.effect op)), .cons (.arg .head) .nil, fun i => i.elim0⟩
  .bind node (fun i => i.elim0)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private def loop (op : SourceEffect dataPorts bodyPorts) :
    Term source.base.op dataPorts [] [dataPorts] dataPorts :=
  .bind (thetaVertex [bodyPorts]) (fun _ => body op)
    (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private abbrev choice : Node source.base.op args [] dataPorts :=
  ⟨args, .base (.gamma 0), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
    Fin.cases [dataPorts] (fun _ => [])⟩

private def program (op : SourceEffect dataPorts bodyPorts) :
    Term source.base.op args [] [dataPorts] dataPorts :=
  .bind choice
    (Fin.cases (motive := fun i => Term source.base.op dataPorts [] (choice.childSigs i) dataPorts)
      (loop op) (fun _ => .ret (.cons (.arg .head) .nil)))
    (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def equation : Equation source :=
  ⟨args, dataPorts, [dataPorts], [dataPorts],
    (program .guarded).toGraph, (program .restart).toGraph⟩

private abbrev value : Unit → Type := fun _ => Nat
private def data (n : Nat) : Tuple (Values value) dataPorts := .cons n .nil
private def input (arm : Fin 2) : Tuple (Values value) args := .cons ⟨arm⟩ (data 0)

private def tick (guarded : Bool) (input : Tuple (Values value) dataPorts) :
    StateT Nat Part (Tuple (Values value) bodyPorts) :=
  StateT.mk fun store =>
    let n : Nat := input.get .head
    if guarded && n == 1 then Part.none
    else Part.some (OrderedState.tagged true (data (n + 1), store + 1))

private def targetModel : Model target Nat where
  value := value
  runPure op := nomatch op
  effect
    | .tryTick => tick true
    | .tick => tick false

private abbrev sourceModel := reduct migrate targetModel

private def attempt : Block SourceEffect value Nat :=
  ⟨[(0, 0), (0, 0)], 0, dataPorts, bodyPorts, .guarded, data 1, 5⟩

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem firstRestart :
    Restart sourceModel (fun x => runOpen sourceModel (body .guarded) x.1 PUnit.unit x.2)
      (data 0, 4) (data 1, 5) := by
  simp only [Restart, runOpen, body, Term.denoteOpenWith, Kind.denoteWith, StateT.run_bind,
    Part.bind_eq_bind]
  change _ ∈ (Part.some (OrderedState.tagged true (data 1, 5))).bind _
  rw [Part.bind_some]
  exact Part.mem_some _

private theorem blocked :
    abnormal sourceModel equation.lhs (input 0) 4 (.blocked attempt) := by
  unfold abnormal equation
  rw [Term.toTerm_toGraph]
  apply Or.inl
  apply Or.inl
  apply Or.inl
  refine ⟨(data 1, 5), Relation.ReflTransGen.single firstRestart, ?_⟩
  apply Or.inl
  exact ⟨Part.not_none_dom, rfl⟩

private theorem productive :
    abnormal sourceModel equation.rhs (input 0) 4 .diverges := by
  unfold abnormal equation
  rw [Term.toTerm_toGraph]
  apply Or.inl
  apply Or.inl
  apply Or.inr
  refine ⟨rfl, fun n => (data n, 4 + n), rfl, ?_⟩
  intro n
  simp only [Restart, runOpen, body, Term.denoteOpenWith, Kind.denoteWith, StateT.run_bind,
    Part.bind_eq_bind]
  change _ ∈ (Part.some (OrderedState.tagged true (data (n + 1), 4 + n + 1))).bind _
  rw [Part.bind_some]
  exact Part.mem_some _

private def translated : Equation target := Equation.map migrate equation

private theorem migratedBlock : abnormal targetModel translated.lhs (input 0) 4
    (.blocked ⟨[(0, 0), (0, 0)], 0, dataPorts, bodyPorts, .tryTick, data 1, 5⟩) :=
  (abnormal_map_iff migrate targetModel equation.lhs (input 0) 4 (.blocked attempt)).mpr blocked

private theorem migratedDivergence : abnormal targetModel translated.rhs (input 0) 4 .diverges :=
  (abnormal_map_iff migrate targetModel equation.rhs (input 0) 4 .diverges).mpr productive

-- The bypass arm returns its whole input and leaves the store untouched.
example : observe targetModel translated.lhs (input 1) 4 = Part.some (data 0, 4) := by
  change observe targetModel (Institution.mapGraph (Signature.Hom.opcodeMap migrate) equation.lhs)
    (input 1) 4 = _
  rw [observe_map]
  unfold observe equation
  rw [Term.toTerm_toGraph]
  simp only [runOpen, program, Term.denoteOpenWith, StateT.run_bind, Part.bind_eq_bind]
  change (Part.some (data 0, 4)).bind _ = _
  rw [Part.bind_some]
  rfl

-- The selected arm on each side has no finite return. The left stops at
-- the attempted opcode after feedback, while the right keeps restarting.
example : observe targetModel translated.lhs (input 0) 4 = Part.none ∧
    observe targetModel translated.rhs (input 0) 4 = Part.none :=
  ⟨Part.eq_none_iff.mpr fun _ returned =>
    OrderedState.Partial.return_excludes_abnormal _ _ _ _ returned _ migratedBlock,
    Part.eq_none_iff.mpr fun _ returned =>
    OrderedState.Partial.return_excludes_abnormal _ _ _ _ returned _ migratedDivergence⟩

private abbrev dialectInst : Inst.{1, 0, 0, 1, 1} := inst Unit Nat

example : ¬ (dialectInst.I.obj source).Sat
    ((dialectInst.I.map migrate).mod.obj (Discrete.mk targetModel)) equation := by
  intro sat
  have migrated := ((dialectInst.I.map migrate).sat (Discrete.mk targetModel) equation).mpr sat
  have erroneouslyBlocked := ((migrated (input 0) 4).2 _).mp migratedBlock
  have clash := OrderedState.Partial.abnormal_unique _ _ _ _ erroneouslyBlocked migratedDivergence
  cases clash

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Tests

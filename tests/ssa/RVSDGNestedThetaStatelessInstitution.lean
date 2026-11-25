module

import Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Tests

open CategoryTheory Silmaril.Logic.Institution Silmaril.Elgot
open OrderedRuntime.Structured (Ty Data Values newestIndex newestPort)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev carrier : Ports (Ty Unit) := [.value ()]
private abbrev tagged : Ports (Ty Unit) := .control 2 :: carrier
private abbrev dataOK : Data carrier := .value .nil
private abbrev taggedOK : Data tagged := .control dataOK

private inductive Source : Dialect Unit Unit where
  | tick : Source carrier tagged
  | spin : Source carrier tagged

private inductive Target : Dialect Unit Unit where
  | advance : Target carrier tagged
  | repeat : Target carrier tagged

private abbrev source : Signature Unit := ⟨Source, fun op => by cases op <;> exact ⟨dataOK, taggedOK⟩⟩
private abbrev target : Signature Unit := ⟨Target, fun op => by cases op <;> exact ⟨dataOK, taggedOK⟩⟩

private def relabel : RVSDG.Institution.OpcodeMap Source Target
  | _, _, .tick => .advance
  | _, _, .spin => .repeat

private def migrate : source ⟶ target := Signature.rename relabel

private def body (op : Source carrier tagged) : Term source.op carrier [] [tagged] tagged :=
  .bind ⟨carrier, .base (.simple (.pure op)), .cons (.arg .head) .nil, fun i => i.elim0⟩
    (fun i => i.elim0)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private def loop (op : Source carrier tagged) : Term source.op carrier [] [carrier] carrier :=
  .bind (thetaVertex [tagged]) (fun _ => body op)
    (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def bypass : Term source.op carrier [] [] carrier := .ret (.cons (.arg .head) .nil)

private abbrev branch (past : List (Ports (Ty Unit))) : Node source.op tagged past carrier :=
  ⟨tagged, .base (.gamma 0), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
    Fin.cases [carrier] (fun _ => [])⟩

private def program (past : List (Ports (Ty Unit))) (op : Source carrier tagged) :
    Term source.op tagged past [carrier] carrier :=
  .bind (branch past)
    (Fin.cases (motive := fun i => Term source.op carrier [] ((branch past).childSigs i) carrier)
      (loop op) (fun _ => bypass))
    (.ret (.cons (.output (newestIndex carrier past) (newestPort .head past)) .nil))

private def padded : Term source.op tagged [] [carrier,carrier] carrier :=
  .bind ⟨tagged, .base (.gamma 0), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), fun _ => []⟩
    (fun _ => bypass) (program [carrier] .tick)

private theorem loop_ok (op : Source carrier tagged) : NoState (loop op) :=
  ⟨dataOK, dataOK, fun _ => ⟨dataOK, taggedOK, fun i => i.elim0, dataOK, taggedOK⟩, dataOK, dataOK⟩

private theorem program_ok (past : List (Ports (Ty Unit))) (op : Source carrier tagged) : NoState (program past op) :=
  ⟨taggedOK, dataOK, Fin.cases (motive := fun i =>
    NoState (Fin.cases (motive := fun j => Term source.op carrier [] ((branch past).childSigs j) carrier)
      (loop op) (fun _ => bypass) i)) (loop_ok op) (fun _ => ⟨dataOK, dataOK⟩), taggedOK, dataOK⟩

private theorem padded_ok : NoState padded :=
  ⟨taggedOK, dataOK, fun _ => ⟨dataOK, dataOK⟩, program_ok [carrier] .tick⟩

private def valid : Equation source :=
  ⟨⟨tagged, carrier, [carrier], [carrier,carrier], (program [] .tick).toGraph, padded.toGraph⟩, by
    simp only [Term.toTerm_toGraph]
    exact ⟨program_ok [] .tick, padded_ok⟩⟩

private def falseEquation : Equation source :=
  ⟨⟨tagged, carrier, [carrier], [carrier], (program [] .tick).toGraph, (program [] .spin).toGraph⟩, by
    simp only [Term.toTerm_toGraph]
    exact ⟨program_ok [] .tick, program_ok [] .spin⟩⟩

private theorem body_run (m : Model source) (op : Source carrier tagged)
    (x : Tuple (Values m.value) carrier) :
    (body op).denoteOpenWith m.partial x PUnit.unit = Part.some (m.run op x) := by
  cases x with
  | cons n rest =>
    cases rest
    simp only [body, Term.denoteOpenWith, Kind.denoteWith, Part.bind_eq_bind]
    change (Part.some (m.run op (.cons n .nil))).bind _ = _
    rw [Part.bind_some]
    cases m.run op (.cons n .nil) with
    | cons _ xs => cases xs with
      | cons _ rest => cases rest; rfl

private noncomputable def chosen (m : Model source) (op : Source carrier tagged) (i : Fin 2)
    (x : Tuple (Values m.value) carrier) : Part (Tuple (Values m.value) carrier) :=
  Fin.cases (iter (stepWith fun p => Part.some (m.run op p)) x) (fun _ => Part.some x) i

private theorem loop_run (m : Model source) (op : Source carrier tagged)
    (x : Tuple (Values m.value) carrier) :
    (loop op).denoteOpenWith m.partial x PUnit.unit = iter (stepWith fun p => Part.some (m.run op p)) x := by
  cases x with
  | cons n rest =>
    cases rest
    simp only [loop, Term.denoteOpenWith, Kind.denoteWith, body_run, Part.bind_eq_bind]
    change (iter (stepWith fun p => Part.some (m.run op p)) (.cons n .nil)).bind
      (fun p => Part.some (Tuple.cons (p.get .head) .nil)) = _
    have repack (p : Tuple (Values m.value) carrier) : (Tuple.cons (p.get .head) .nil) = p := by
      cases p with
      | cons _ rest => cases rest; rfl
    simp only [repack, Part.bind_some_right]

private theorem newest_read (m : Model source) (past : List (Ports (Ty Unit)))
    (locals : Locals (Values m.value) past) (p : Tuple (Values m.value) carrier) :
    ((locals.snoc p).get (newestIndex carrier past)).get (newestPort .head past) = p.get .head := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact ih locals.2

private theorem program_run (m : Model source) (op : Source carrier tagged) (past : List (Ports (Ty Unit)))
    (locals : Locals (Values m.value) past) (i : Fin 2) (x : Tuple (Values m.value) carrier) :
    (program past op).denoteOpenWith m.partial (.cons ⟨i⟩ x) locals = chosen m op i x := by
  have kids : (Fin.cases (motive := fun j => Term source.op carrier [] ((branch past).childSigs j) carrier)
      (loop op) (fun _ => bypass) i).denoteOpenWith m.partial x PUnit.unit = chosen m op i x := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact loop_run m op x
    · cases x with | cons _ rest => cases rest; rfl
  cases x with
  | cons n rest =>
    cases rest
    simp only [program, Term.denoteOpenWith, Kind.denoteWith, Part.bind_eq_bind]
    change ((Fin.cases (motive := fun j => Term source.op carrier [] ((branch past).childSigs j) carrier)
        (loop op) (fun _ => bypass) i).denoteOpenWith m.partial (.cons n .nil) PUnit.unit).bind
        (fun p => Part.some (Tuple.cons (((locals.snoc p).get (newestIndex carrier past)).get
          (newestPort .head past)) .nil)) = _
    rw [kids]
    have ret (p : Tuple (Values m.value) carrier) :
        (Tuple.cons (((locals.snoc p).get (newestIndex carrier past)).get (newestPort .head past)) .nil) = p := by
      rw [newest_read]
      cases p with | cons _ rest => cases rest; rfl
    simp only [ret, Part.bind_some_right]

private theorem valid_in_every_model (m : Model source) : valid.Holds m := by
  intro x
  cases x with
  | cons i x =>
    change observe m (program [] .tick).toGraph (.cons i x) = observe m padded.toGraph (.cons i x)
    obtain ⟨i⟩ := i
    unfold observe NestedTheta.Partial.observe
    rw [Term.toTerm_toGraph, Term.toTerm_toGraph, program_run]
    simp only [padded, Term.denoteOpenWith, Kind.denoteWith, Part.bind_eq_bind]
    change _ = (bypass.denoteOpenWith m.partial x PUnit.unit).bind _
    cases x with
    | cons n rest =>
      cases rest
      change _ = (Part.some (Tuple.cons n .nil)).bind _
      rw [Part.bind_some]
      exact (program_run m .tick [carrier] (_, PUnit.unit) i (.cons n .nil)).symm

private abbrev value : Unit → Type := fun _ => Nat
private def data (n : Nat) : Tuple (Values value) carrier := .cons n .nil

private def targetModel : Model target where
  value := value
  run
    | .advance, x =>
      let n : Nat := x.get .head
      if n < 2 then .cons ⟨1⟩ (data (n + 1)) else .cons ⟨0⟩ x
    | .repeat, x => .cons ⟨1⟩ x

private abbrev sourceModel := reduct migrate targetModel
private def input (i : Fin 2) (n : Nat) : Tuple (Values value) tagged := .cons ⟨i⟩ (data n)

private theorem tick_returns :
    observe sourceModel falseEquation.val.lhs (input 0 0) = Part.some (data 2) := by
  unfold observe NestedTheta.Partial.observe falseEquation
  rw [Term.toTerm_toGraph]
  change (program [] .tick).denoteOpenWith sourceModel.partial (.cons ⟨0⟩ (data 0)) PUnit.unit = _
  rw [program_run]
  change iter (stepWith fun p => Part.some (sourceModel.run .tick p)) (data 0) = _
  rw [Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  refine .more (a' := data 1) ?_ (.more (a' := data 2) ?_ (.done ?_))
  all_goals
    simp only [stepWith, Bind.kleisliRight, Part.pure_eq_some, Part.bind_eq_bind, Part.bind_some]
    exact Part.mem_some_iff.mpr rfl

private theorem spin_diverges :
    Diverges sourceModel falseEquation.val.rhs (input 0 0) := by
  unfold Diverges observe NestedTheta.Partial.observe falseEquation
  rw [Term.toTerm_toGraph]
  change ¬ ((program [] .spin).denoteOpenWith sourceModel.partial (.cons ⟨0⟩ (data 0)) PUnit.unit).Dom
  rw [program_run]
  change ¬ (iter (stepWith fun p => Part.some (sourceModel.run .spin p)) (data 0)).Dom
  intro finite
  have run := Part.get_mem finite
  rw [Silmaril.Elgot.Part.mem_iter_iff] at run
  have impossible (start result : Tuple (Values value) carrier)
      (path : Silmaril.Elgot.Part.Runs (stepWith fun p => Part.some (sourceModel.run .spin p)) start result) :
      False := by
    induction path with
    | done h =>
      simp only [stepWith, Bind.kleisliRight, Part.pure_eq_some, Part.bind_eq_bind, Part.bind_some] at h
      have clash := Part.mem_some_iff.mp h
      cases clash
    | more _ _ ih => exact ih
  exact impossible _ _ run

private def stateModel : Institution.Partial.Model target.ordered Nat := expand targetModel

example : Institution.Partial.Equation.Holds (sentenceInclusion target (valid.map migrate)) stateModel :=
  (included_holds _ _).mpr ((valid.satisfaction migrate targetModel).mpr (valid_in_every_model sourceModel))

private theorem false_refuted : ¬ falseEquation.Holds sourceModel := by
  intro holds
  exact spin_diverges (by rw [← holds (input 0 0), tick_returns]; exact Part.some_dom _)

example : ¬ Institution.Partial.Equation.Holds (sentenceInclusion target (falseEquation.map migrate)) stateModel :=
  fun h => false_refuted ((falseEquation.satisfaction migrate targetModel).mp ((included_holds _ _).mp h))

-- The selected θ takes two restarts. The ordered reading returns the exact initial store.
example : OrderedState.Partial.observe stateModel (falseEquation.map migrate).val.lhs (input 0 0) 17 =
    Part.some (data 2, 17) := by
  rw [observe_forget]
  change Part.map _ (observe targetModel
    (Institution.mapGraph (Institution.Partial.Signature.Hom.opcodeMap migrate) falseEquation.val.lhs) (input 0 0)) = _
  rw [observe_map, tick_returns, Part.map_some]

example : OrderedState.Partial.abnormal stateModel (falseEquation.map migrate).val.rhs (input 0 0) 17 .diverges := by
  apply (diverges_iff _ _ _ _).mpr
  unfold Diverges
  change ¬ (observe targetModel
    (Institution.mapGraph (Institution.Partial.Signature.Hom.opcodeMap migrate) falseEquation.val.rhs) (input 0 0)).Dom
  rw [observe_map]
  exact spin_diverges

-- The same spinning θ is unreachable when γ selects its bypass arm.
example : OrderedState.Partial.observe stateModel (falseEquation.map migrate).val.rhs (input 1 3) 17 =
    Part.some (data 3, 17) := by
  rw [observe_forget]
  change Part.map _ (observe targetModel
    (Institution.mapGraph (Institution.Partial.Signature.Hom.opcodeMap migrate) falseEquation.val.rhs) (input 1 3)) = _
  rw [observe_map]
  unfold observe NestedTheta.Partial.observe falseEquation
  rw [Term.toTerm_toGraph]
  change Part.map (fun p : Tuple (Values value) carrier => (p, (17 : Nat)))
    ((program [] .spin).denoteOpenWith sourceModel.partial (.cons ⟨1⟩ (data 3)) PUnit.unit) = _
  rw [program_run]
  rfl

-- An empty effect family alone would still let the ambient syntax route state ports.
example : ¬ NoState
    (.ret (.cons (.arg .head) .nil) :
      Term source.op [.state PUnit.unit] [] [] [.state PUnit.unit]) := by
  intro h
  cases h.1

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Tests

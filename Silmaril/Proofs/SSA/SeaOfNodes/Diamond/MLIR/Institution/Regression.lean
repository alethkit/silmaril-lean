module

import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution

open CategoryTheory
open RVSDG (Tuple)

private abbrev word : ValueSort Unit := .data ()
private abbrev inputs : List (ValueSort Unit) := [.predicate, word]
private abbrev sigs : List (List (Diamond.Ty Unit)) := [[.value word], [.value word]]

private inductive Arithmetic : Diamond.Signature.{0, 0} Unit
  | inc : Arithmetic [word] word
  | double : Arithmetic [word] word

private abbrev sig : Diamond.Institution.Signature.{0, 0} Unit := ⟨Arithmetic⟩

private def arithmetic : Model.{0, 0, 0} sig.op where
  value _ := Nat
  run
    | .inc, .cons n .nil => Nat.succ n
    | .double, .cons n .nil => Nat.add n n

private def swap : sig ⟶ sig :=
  ⟨fun | .inc => .double | .double => .inc⟩

private def identify : sig ⟶ sig :=
  ⟨fun | .inc => .inc | .double => .inc⟩

private def diamond (first second : Arithmetic [word] word) : Graph sig.op inputs sigs word where
  dataflow :=
    .cons first (.cons (.arg (.tail .head)) .nil)
      (.cons second (.cons (.arg (.tail .head)) .nil) .nil)
  predicate := .arg .head
  phi := ⟨⟨.onFalse⟩, fun
    | .first => .output (1 : Fin 2) .head
    | .second => .output (0 : Fin 2) .head⟩

private def equation : Diamond.Institution.Equation sig :=
  ⟨inputs, word, sigs, sigs, diamond .inc .double, diamond .double .inc⟩

example : translate (equation.map (identify ≫ swap)) =
    ((translate equation).map ((signatureFunctor Unit).map identify)).map
      ((signatureFunctor Unit).map swap) := by
  rw [Diamond.Institution.Equation.map_comp, translate_map, translate_map]

example : (model arithmetic).reduct ((signatureFunctor Unit).map (identify ≫ swap)) =
    model (Diamond.Institution.reduct identify (Diamond.Institution.reduct swap arithmetic)) := by
  exact (model_reduct (identify ≫ swap) arithmetic).trans
    (congrArg model (Diamond.Institution.reduct_comp identify swap arithmetic))

example : (translate (equation.map (identify ≫ swap))).Holds (model arithmetic) :=
  (satisfaction_induced _ arithmetic).mpr (fun _ => rfl)

-- Keep the induced carriers and primitive interpretations, but use arm 0 at every gamma.
private def firstArmModel {Data : Type} {P : Diamond.Institution.Signature.{0, 0} Data}
    (m : Model.{0, 0, 0} P.op) : Silmaril.MLIR.Institution.Model (target P) where
  carrier := (model m).carrier
  op
    | .simple op, args, bodies => (model m).op (.simple op) args bodies
    | .gamma _ _ _, args, bodies => bodies ⟨0, Nat.zero_lt_succ _⟩ (fun i => args i.succ)

private abbrev predicatePort : Diamond.Ty Unit := .value .predicate

private abbrev selection : RVSDG.MLIR.Graph.Op (source sig.op)
    (RVSDG.MLIR.Graph.profile [.control 2] [predicatePort] 2 [] [predicatePort]) :=
  .gamma [] [predicatePort] 0

example : (firstArmModel arithmetic).op selection
    (fun i => Fin.cases (ULift.up (1 : Fin 2)) (fun j => j.elim0) i)
    (fun branch _ i => Fin.cases (ULift.up (branch.val == 1)) (fun j => j.elim0) i)
    (0 : Fin 1) = ULift.up false := rfl

example : (model arithmetic).op selection
    (fun i => Fin.cases (ULift.up (1 : Fin 2)) (fun j => j.elim0) i)
    (fun branch _ i => Fin.cases (ULift.up (branch.val == 1)) (fun j => j.elim0) i)
    (0 : Fin 1) = ULift.up true := rfl

private def singletonModel {Data : Type} (P : Diamond.Institution.Signature.{0, 0} Data) :
    Silmaril.MLIR.Institution.Model (target P) where
  carrier _ := Unit
  op _ _ _ _ := ()

private def predicateGraph {Data : Type} (P : Diamond.Institution.Signature.{0, 0} Data)
    (useSecond : Bool) : Graph P.op [.predicate, .predicate] [] .predicate where
  dataflow := .nil
  predicate := .arg .head
  phi := ⟨⟨.onTrue⟩, fun
    | .first => .arg .head
    | .second => if useSecond then .arg (.tail .head) else .arg .head⟩

private def witness {Data : Type} (P : Diamond.Institution.Signature.{0, 0} Data) :
    Diamond.Institution.Equation P :=
  ⟨[.predicate, .predicate], .predicate, [], [], predicateGraph P false, predicateGraph P true⟩

/-- Collapsing the Boolean carrier rules out an all-target-model reduct. -/
example {Data : Type} (P : Diamond.Institution.Signature.{0, 0} Data) :
    ¬ ∃ sourceModel : Model.{0, 0, 0} P.op, ∀ e : Diamond.Institution.Equation P,
      (translate e).Holds (singletonModel P) ↔ e.Holds sourceModel := by
  rintro ⟨sourceModel, sat⟩
  have targetHolds : (translate (witness P)).Holds (singletonModel P) :=
    fun _ _ => @Subsingleton.elim Unit _ _ _
  have disagree := ((sat (witness P)).mp targetHolds) (.cons ⟨false⟩ (.cons ⟨true⟩ .nil))
  change (ULift.up false : ULift Bool) = ULift.up true at disagree
  cases disagree

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution

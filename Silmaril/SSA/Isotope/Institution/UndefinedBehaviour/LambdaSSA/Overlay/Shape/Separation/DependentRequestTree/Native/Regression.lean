module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction

open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent (pack)
open Category.FiniteIteration.CFG.Dependent.Native (withExitUB)
open LambdaSSA.Region (packedExitType)
open TwoRequest (Exits Tag exit_type)

private inductive Op where
  | choose
  | left
  | right
  deriving DecidableEq

private abbrev replies : Op → List Syntax.Ty
  | .choose => List.replicate 2 .unit
  | .left | .right => List.replicate 1 .unit

private def argType : Op → Syntax.Ty
  | .left => .coprod .unit .unit
  | .choose | .right => .unit

private instance : HasTy Op Syntax.Ty := ⟨argType, fun f => packedExitType (replies f)⟩

private abbrev operands (useRight : Bool) : Operands Op where
  replies := replies
  argument f := match f with
    | .choose | .right => .unit
    | .left => if useRight then .inr .unit else .inl .unit
  target _ := rfl

private theorem unit_at {n : Nat}
    (i : Fin (List.replicate n (.unit : Syntax.Ty)).length) :
    (List.replicate n (.unit : Syntax.Ty)).get i = .unit := by simp

private abbrev Packets : List Syntax.Ty := List.replicate 4 .unit

/-- A written diamond. The entry reply chooses a different native request
on each branch. Both request blocks jump to the same written exit block. -/
private def diamond (useRight : Bool) (exit : Tag) : Table (operands useRight) Packets where
  entry := (0 : Fin 4)
  input := .unit
  row i := match i.val with
    | 0 => .request .choose (fun (j : Fin 2) => if j = 0 then (1 : Fin 4) else (2 : Fin 4))
        (fun j => (unit_at (n := 4) _).trans (unit_at (n := 2) j).symm)
    | 1 => .request .left (fun _ => (3 : Fin 4))
        (fun j => (unit_at (n := 4) _).trans (unit_at (n := 1) j).symm)
    | 2 => .request .right (fun _ => (3 : Fin 4))
        (fun j => (unit_at (n := 4) _).trans (unit_at (n := 1) j).symm)
    | _ => .exit exit
  selected i := i == (1 : Fin 2)

private abbrev lower := diamond false 0
private abbrev upper := diamond false 1

private theorem lower_checked : lower.check lower.native = true := rfl
private theorem upper_checked : upper.check upper.native = true := rfl

example : (3 : Fin 4) ∈ lower.targets (1 : Fin 4) ∧ (3 : Fin 4) ∈ lower.targets (2 : Fin 4) := by
  decide

/-- Exactly the same key, typing, and routes with a different well-typed
operand at the left call site. The original operand certificate rejects it. -/
example : lower.extract? (diamond true 0).native = none := rfl

example : (lower.extract? lower.native).isSome = true := rfl

private def primitives : Syntax.Primitives Op 3 := fun f a _ =>
  match f with
  | .choose => .ret (pack (L := replies .choose) ⟨(0 : Fin 2), ⟨.unit, .unit⟩⟩) 1
  | .left => match a.val with
    | .inl _ => .ret (pack (L := replies .left) ⟨(0 : Fin 1), ⟨.unit, .unit⟩⟩) 2
    | _ => .fault 2
  | .right => .diverge

private abbrev M := Syntax.model primitives Syntax.emptyBindings

private def unitPayload : Syntax.Payload (.unit : Syntax.Ty) := ⟨.unit, .unit⟩

private theorem observe_diamond (flip : Bool) (j : Tag)
    (ok : (diamond flip j).check (diamond flip j).native = true) :
    Shape.denote (withExitUB (diamond flip j).native (diamond flip j).selected) M 0 =
      if flip then WithTop.some {Outcome.fault (2 : Fin 3)}
      else if (diamond flip j).selected j then ⊤
      else WithTop.some {Outcome.ret j Value.unit (2 : Fin 3)} := by
  let g := diamond flip j
  let O := operands flip
  let e := Syntax.emptyBindings
  rw [← g.observe ok, Table.extract, Table.extractAt.eq_def]
  change Shape.denote (.lsubst
    (CFG.Dependent.packedRequest Op.choose (O.signature.argument Op.choose) (O.target Op.choose)) _)
    (Syntax.model primitives e) (0 : Fin 3) = _
  erw [CFG.Dependent.observe_packedRequest_bind]
  have ranked : (g.ranks.get (1 : Fin 4)).isSome = true := rfl
  change Shape.denote ((g.extractAt (1 : Fin 4) ranked).region O.signature)
    (Syntax.model primitives (e.push unitPayload)) (1 : Fin 3) = _
  rw [Table.extractAt.eq_def]
  change Shape.denote (.lsubst
    (CFG.Dependent.packedRequest Op.left (O.signature.argument Op.left) (O.target Op.left)) _)
    (Syntax.model primitives (e.push unitPayload)) (1 : Fin 3) = _
  erw [CFG.Dependent.observe_packedRequest_bind]
  cases flip
  · have last : ((diamond false j).ranks.get (3 : Fin 4)).isSome = true := rfl
    change Shape.denote (((diamond false j).extractAt (3 : Fin 4) last).region (operands false).signature)
      (Syntax.model primitives ((e.push unitPayload).push unitPayload)) (2 : Fin 3) = _
    rw [Table.extractAt.eq_def]
    change Shape.denote ((Tree.stop (if (diamond false j).selected j then .ub else .ret j)).region
        (operands false).signature) (Syntax.model primitives ((e.push unitPayload).push unitPayload))
        (2 : Fin 3) =
      if (diamond false j).selected j then ⊤ else WithTop.some {Outcome.ret j Value.unit (2 : Fin 3)}
    by_cases selected : (diamond false j).selected j = true
    · simp only [ite_eq_left selected]
      rfl
    · simp only [ite_eq_right selected]
      exact CFG.observe_jump (L := Exits) primitives ((e.push unitPayload).push unitPayload)
        j (exit_type j) .unit (2 : Fin 3)
  · rfl

private theorem lower_observes : Shape.denote (withExitUB lower.native lower.selected) M 0 =
    WithTop.some {Outcome.ret (0 : Fin 2) Value.unit (2 : Fin 3)} :=
  observe_diamond false 0 lower_checked

private theorem upper_observes : Shape.denote (withExitUB upper.native upper.selected) M 0 = ⊤ :=
  observe_diamond false 1 upper_checked

example : Shape.denote (withExitUB (diamond true 0).native (diamond true 0).selected) M 0 =
    WithTop.some {Outcome.fault (2 : Fin 3)} :=
  observe_diamond true 0 rfl

example : ∃ (n : Nat) (probe : Prefix (operands false).replies n),
    n ≤ min (upper.extract (upper.checked_rank upper_checked)).depth
      (lower.extract (lower.checked_rank lower_checked)).depth ∧
    ¬ Shape.denote (withExitUB upper.native upper.selected) ((operands false).signature.model probe.handler) 0 ≤
      Shape.denote (withExitUB lower.native lower.selected) ((operands false).signature.model probe.handler) 0 := by
  apply exists_countermodel upper_checked lower_checked
  intro le
  have test := (finite_refines_iff upper_checked lower_checked).mpr le 3 primitives 0
  change Shape.denote (withExitUB upper.native upper.selected) M 0 ≤
    Shape.denote (withExitUB lower.native lower.selected) M 0 at test
  rw [upper_observes, lower_observes] at test
  exact WithTop.not_top_le_coe _ test

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.finite_refines_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms finite_refines_iff

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction

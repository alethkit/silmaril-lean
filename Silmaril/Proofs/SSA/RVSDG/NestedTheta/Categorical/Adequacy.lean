module

public import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Defs
public import Silmaril.Semantics.Elgot.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Categorical.Proofs

open Silmaril.Elgot (iter)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args ins outs carried : Ports (PortType V S)}
variable {past sigs : List (Ports (PortType V S))}

private theorem route_injective (m : Model.{u, v, w} Op) :
    Function.Injective (route (carried := carried) m) := by
  apply Function.LeftInverse.injective
    (g := Sum.elim (Theta.bodyResult m false) (Theta.bodyResult m true))
  intro result
  cases result with
  | cons tagged payload =>
    change ULift.{w} (Fin 2) at tagged
    obtain ⟨tag⟩ := tagged
    revert tag
    exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))

private theorem route_eq_iff (m : Model.{u, v, w} Op)
    (result : Tuple m.Val (Theta.BodyResults carried)) (again : Bool) (output : Tuple m.Val carried) :
    route m result = (if again then .inr output else .inl output) ↔
      result = Theta.bodyResult m again output := by
  have routed : route m (Theta.bodyResult m again output) =
      (if again then .inr output else .inl output) := by cases again <;> rfl
  rw [← routed]
  exact (route_injective m).eq_iff

private theorem step_mem (m : Model.{u, v, w} Op)
    (body : Tuple m.Val carried → _root_.Part (Tuple m.Val (Theta.BodyResults carried)))
    (input output : Tuple m.Val carried) (again : Bool) :
    (if again then .inr output else .inl output) ∈ step m body input ↔
      Theta.bodyResult m again output ∈ body input := by
  change _ ∈ (body input).bind (fun result => _root_.Part.some (route m result)) ↔ _
  simp only [_root_.Part.mem_bind_iff, _root_.Part.mem_some_iff]
  constructor
  · rintro ⟨result, member, routed⟩
    rwa [(route_eq_iff m result again output).mp routed.symm] at member
  · intro member
    exact ⟨_, member, ((route_eq_iff m _ again output).mpr rfl).symm⟩

private theorem kind_mem (m : Model.{u, v, w} Op) (kind : Kind Op ins outs)
    (eval : Fin kind.arity → Tuple m.Val kind.entry → _root_.Part (Tuple m.Val kind.exit))
    (exec : Fin kind.arity → Tuple m.Val kind.entry → Tuple m.Val kind.exit → Prop)
    (child_iff : ∀ i x y, y ∈ eval i x ↔ exec i x y)
    (input : Tuple m.Val ins) (output : Tuple m.Val outs) :
    output ∈ kind.denote m eval input ↔ kind.Exec m exec input output := by
  cases kind with
  | base shape =>
    cases shape with
    | simple opcode =>
      exact _root_.Part.mem_some_iff.trans eq_comm
    | gamma n =>
      cases input with
      | cons tag payload => exact child_iff tag.down payload output
  | theta =>
    let body : Tuple m.Val ins → _root_.Part (Tuple m.Val (Theta.BodyResults ins)) := eval (0 : Fin 1)
    change output ∈ iter (step m body) input ↔
      Theta.Iterate (fun x again y => exec (0 : Fin 1) x (Theta.bodyResult m again y)) input output
    rw [Silmaril.Elgot.Part.mem_iter_iff]
    have body_iff (x y : Tuple m.Val ins) (again : Bool) :
        (if again then .inr y else .inl y) ∈ step m body x ↔
          exec (0 : Fin 1) x (Theta.bodyResult m again y) :=
      (step_mem m body x y again).trans (child_iff _ _ _)
    constructor
    · intro run
      induction run with
      | done last => exact .stop ((body_iff _ _ false).mp last)
      | more next _ ih => exact .again ((body_iff _ _ true).mp next) ih
    · intro run
      induction run with
      | stop last => exact .done ((body_iff _ _ false).mpr last)
      | again next _ ih => exact .more ((body_iff _ _ true).mpr next) ih

theorem mem_denoteOpen (m : Model.{u, v, w} Op) (t : Term Op args past sigs outs)
    (input : Tuple m.Val args) (locals : Locals m.Val past) (output : Tuple m.Val outs) :
    output ∈ t.denoteOpen (M := _root_.Part) m input locals ↔ t.Exec m input locals output := by
  induction t with
  | ret wires => exact _root_.Part.mem_some_iff.trans eq_comm
  | bind node children rest child_iff rest_iff =>
    rw [Term.denoteOpen, Term.Exec]
    change _ ∈ _root_.Part.bind _ _ ↔ _
    rw [_root_.Part.mem_bind_iff]
    exact exists_congr fun result =>
      (kind_mem m node.kind _ _ (fun i x y => child_iff i x PUnit.unit y) _ result).and
        (rest_iff input (locals.snoc result) output)

end Silmaril.SSA.RVSDG.NestedTheta.Categorical.Proofs

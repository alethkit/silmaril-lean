module

public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Defs
public import Silmaril.Semantics.ElgotMonads.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Proofs

open OrderedRuntime
open Structured (Instruction Values Ty)
open Silmaril.Elgot (iter)

universe u v w
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args ins outs carried : Ports (Ty V)} {past sigs : List (Ports (Ty V))}
variable {value : V → Type (max u w)}

private theorem distributes_injective :
    Function.Injective (fun result : Configuration value σ (Theta.BodyResults carried) =>
      Silmaril.Elgot.StateT.distribute (routeValue result.1, result.2)) := by
  apply Function.LeftInverse.injective (g := Sum.elim (tagged false) (tagged true))
  rintro ⟨result, state⟩
  cases result with
  | cons selector payload =>
    change ULift.{max u w} (Fin 2) at selector
    obtain ⟨tag⟩ := selector
    revert tag
    exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))

private theorem step_mem
    (body : Tuple (Values value) carried → StateT σ _root_.Part (Tuple (Values value) (Theta.BodyResults carried)))
    (input output : Configuration value σ carried) (again : Bool) :
    (if again then .inr output else .inl output) ∈ Silmaril.Elgot.StateT.body (stepWith body) input ↔
      tagged again output ∈ (body input.1).run input.2 := by
  simp only [Silmaril.Elgot.StateT.body, stepWith, Bind.kleisliRight, StateT.run_bind, StateT.run_pure,
    bind_assoc, pure_bind, Function.comp_apply]
  change _ ∈ ((body input.1).run input.2).bind (fun result =>
    _root_.Part.some (Silmaril.Elgot.StateT.distribute (routeValue result.1, result.2))) ↔ _
  simp only [_root_.Part.mem_bind_iff, _root_.Part.mem_some_iff]
  have routes : Silmaril.Elgot.StateT.distribute
      (routeValue (tagged again output).1, (tagged again output).2) =
      (if again then .inr output else .inl output) := by
    cases again <;> rfl
  rw [← routes]
  constructor
  · rintro ⟨result, member, eq⟩
    rwa [distributes_injective eq.symm] at member
  · intro member
    exact ⟨_, member, rfl⟩

private theorem kind_mem (m : Structured.Model P E (StateM σ)) (kind : Kind (Instruction P E) ins outs)
    (eval : Fin kind.arity → Tuple (Values m.value) kind.entry →
      StateT σ _root_.Part (Tuple (Values m.value) kind.exit))
    (rel : Fin kind.arity → Configuration m.value σ kind.entry → Configuration m.value σ kind.exit → Prop)
    (child_iff : ∀ i x y, y ∈ (eval i x.1).run x.2 ↔ rel i x y)
    (input : Configuration m.value σ ins) (output : Configuration m.value σ outs) :
    output ∈ (kind.denoteWith (interpretation m) eval input.1).run input.2 ↔ kindExec m kind rel input output := by
  cases kind with
  | base shape =>
    cases shape with
    | simple opcode =>
      rcases input with ⟨input, state⟩
      cases opcode <;> exact _root_.Part.mem_some_iff.trans eq_comm
    | gamma n =>
      rcases input with ⟨input, state⟩
      cases input with
      | cons tag payload => exact child_iff tag.down (payload, state) output
  | theta =>
    let body : Tuple (Values m.value) ins →
        StateT σ _root_.Part (Tuple (Values m.value) (Theta.BodyResults ins)) := eval (0 : Fin 1)
    change output ∈ (iter (stepWith body) input.1).run input.2 ↔
      Theta.Iterate (fun x again y => rel (0 : Fin 1) x (tagged again y)) input output
    rw [Silmaril.Elgot.StateT.run_iter]
    change output ∈ iter (Silmaril.Elgot.StateT.body (stepWith body)) input ↔ _
    rw [Silmaril.Elgot.Part.mem_iter_iff]
    have body_iff (x y : Configuration m.value σ ins) (again : Bool) :
        (if again then .inr y else .inl y) ∈ Silmaril.Elgot.StateT.body (stepWith body) x ↔
          rel (0 : Fin 1) x (tagged again y) :=
      (step_mem body x y again).trans (child_iff _ _ _)
    constructor
    · intro run
      induction run with
      | done last => exact .stop ((body_iff _ _ false).mp last)
      | more next _ ih => exact .again ((body_iff _ _ true).mp next) ih
    · intro run
      induction run with
      | stop last => exact .done ((body_iff _ _ false).mpr last)
      | again next _ ih => exact .more ((body_iff _ _ true).mpr next) ih

theorem mem_denoteOpen (m : Structured.Model P E (StateM σ)) (t : Term (Instruction P E) args past sigs outs)
    (input : Tuple (Values m.value) args) (locals : Locals (Values m.value) past)
    (state : σ) (output : Configuration m.value σ outs) :
    output ∈ (t.denoteOpenWith (interpretation m) input locals).run state ↔
      exec m t input locals state output := by
  induction t generalizing state with
  | ret wires => exact _root_.Part.mem_some_iff.trans eq_comm
  | bind node children rest child_iff rest_iff =>
    rw [exec]
    change output ∈ ((node.kind.denoteWith (interpretation m)
      (fun i x => (children i).denoteOpenWith (interpretation m) x PUnit.unit) (node.inputs.read input locals) >>=
        fun result => rest.denoteOpenWith (interpretation m) input (locals.snoc result)).run state) ↔ _
    rw [StateT.run_bind]
    refine _root_.Part.mem_bind_iff.trans ?_
    exact exists_congr fun result =>
      (kind_mem m node.kind
        (fun i x => (children i).denoteOpenWith (interpretation m) x PUnit.unit)
        (fun i x y => exec m (children i) x.1 PUnit.unit x.2 y)
        (fun i x y => child_iff i x.1 PUnit.unit x.2 y) (node.inputs.read input locals, state) result).and
          (rest_iff input (locals.snoc result.1) result.2 output)

end Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Proofs

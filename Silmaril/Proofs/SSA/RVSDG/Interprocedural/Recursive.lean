module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

theorem linkBindings_eq (m : Machine.{u, v, w} Op) (unitId : Nat) (imports : Tuple m.Val args)
    (term : ModuleTerm Op args past sigs outs) (locals : Locals m.Val past) :
    linkTable m unitId imports past sigs locals term.vertices term.results =
      linkBindings m unitId imports term locals := by
  induction term with
  | ret => rfl
  | bind definition rest ih =>
    simp only [ModuleTerm.vertices, ModuleTerm.results, linkTable, linkBindings]
    exact ih _

private abbrev CallSound (m : Machine.{u, v, w} Op) (depth : Nat) :=
  ∀ {ins outs : Ports (Ty V S)} (callee : m.Val (.value (.function ins outs)))
    (input : Tuple m.Val ins) (output : Tuple m.Val outs),
    invoke m 0 depth callee input = some output → Returns m (.call callee input) output

private theorem node_sound (m : Machine.{u, v, w} Op) (depth : Nat)
    (calls : CallSound m depth) (kind : NestedTheta.Kind (Instruction Op) args outs)
    (cs : Fin kind.arity → List (Ports (Ty V S))) (children : Bodies kind cs)
    (childSound : ∀ k i o, (Job.region (children k) i (PUnit.unit : Locals m.Val [])).run m depth = some o →
      Returns m (.region (children k) i (PUnit.unit : Locals m.Val [])) o)
    (input : Tuple m.Val args) (output : Tuple m.Val outs)
    (evaluated : (Job.node kind cs children input).run m depth = some output) :
    Returns m (.node kind cs children input) output := by
  cases kind with
  | base shape =>
    cases shape with
    | simple opcode =>
      cases opcode with
      | primitive op =>
        have eq : m.primitive op input = output := Option.some.inj evaluated
        exact eq ▸ Returns.primitive op cs children input
      | apply fn =>
        cases input with
        | cons callee arguments => exact .apply (calls callee arguments output evaluated)
    | gamma extra =>
      cases input with
      | cons choice entry =>
        cases choice with
        | control tag => exact .gamma (childSound tag entry output evaluated)
  | theta => cases evaluated

private theorem region_sound (m : Machine.{u, v, w} Op) (depth : Nat)
    (calls : CallSound m depth) (term : NestedTheta.Term (Instruction Op) args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) (output : Tuple m.Val outs)
    (evaluated : (Job.region term entry locals).run m depth = some output) :
    Returns m (.region term entry locals) output := by
  induction term with
  | ret wires =>
    have eq : wires.read entry locals = output := Option.some.inj evaluated
    exact eq ▸ Returns.ret wires entry locals
  | bind node children rest childIH restIH =>
    let first := Job.node node.kind node.childSigs children (node.inputs.read entry locals)
    change (first.run m depth >>= fun value =>
      (Job.region rest entry (locals.snoc value)).run m depth) = some output at evaluated
    cases reached : first.run m depth with
    | none => rw [reached] at evaluated; cases evaluated
    | some value =>
      rw [reached] at evaluated
      exact .bind
        (node_sound m depth calls node.kind node.childSigs children
          (fun k i o => childIH k i PUnit.unit o) _ value reached)
        (restIH entry (locals.snoc value) output evaluated)

theorem call_sound (m : Machine.{u, v, w} Op) (depth : Nat) :
    ∀ {params results : Ports (Ty V S)} (callee : m.Val (.value (.function params results)))
      (input : Tuple m.Val params) (output : Tuple m.Val results),
      invoke m 0 depth callee input = some output → Returns m (.call callee input) output := by
  induction depth with
  | zero =>
    intro _ _ _ _ _ empty
    cases empty
  | succ depth ih =>
    intro params results callee input output evaluated
    let closure := resolve m callee
    exact .call (region_sound m depth (fun callee input output => ih callee input output)
      closure.body.toTerm (Closure.enter Op closure input) PUnit.unit output evaluated)

theorem complete (m : Machine.{u, v, w} Op) {job : Job m outs} {output : Tuple m.Val outs}
    (derivation : Returns m job output) :
    ∃ depth, ∀ bound, depth ≤ bound → job.run m bound = some output := by
  induction derivation with
  | call body ih =>
    obtain ⟨depth, runs⟩ := ih
    refine ⟨depth + 1, fun bound enough => ?_⟩
    cases bound with
    | zero => omega
    | succ bound => exact runs bound (Nat.le_of_succ_le_succ enough)
  | ret wires input locals => exact ⟨0, fun _ _ => rfl⟩
  | @bind args head outs past tail node children rest entry locals value output first more firstIH restIH =>
    obtain ⟨firstDepth, firstRun⟩ := firstIH
    obtain ⟨tailDepth, tailRun⟩ := restIH
    refine ⟨max firstDepth tailDepth, fun depth enough => ?_⟩
    change ((Job.node node.kind node.childSigs children (node.inputs.read entry locals)).run m depth >>=
      fun value => (Job.region rest entry (locals.snoc value)).run m depth) = some output
    rw [firstRun depth (Nat.le_trans (Nat.le_max_left _ _) enough)]
    exact tailRun depth (Nat.le_trans (Nat.le_max_right _ _) enough)
  | primitive opcode cs children input => exact ⟨0, fun _ _ => rfl⟩
  | apply invocation ih => exact ih
  | gamma branch ih => exact ih

theorem call_iff (m : Machine.{u, v, w} Op) (callee : m.Val (.value (.function args outs)))
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    Returns m (.call callee input) output ↔ ∃ depth, invoke m 0 depth callee input = some output := by
  constructor
  · intro returned
    obtain ⟨depth, runs⟩ := complete m returned
    exact ⟨depth, runs depth (Nat.le_refl _)⟩
  · rintro ⟨depth, evaluated⟩
    exact call_sound m depth callee input output evaluated

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Proofs

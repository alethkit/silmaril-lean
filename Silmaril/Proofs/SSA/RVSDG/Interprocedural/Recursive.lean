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

private abbrev CallSound (m : Machine.{u, v, w} Op) (loops depth : Nat) :=
  ∀ {ins outs : Ports (Ty V S)} (callee : m.Val (.value (.function ins outs)))
    (input : Tuple m.Val ins) (output : Tuple m.Val outs),
    invoke m loops depth callee input = some output → Returns m (.call callee input) output

private theorem iteration_sound (m : Machine.{u, v, w} Op) (loops depth remaining : Nat)
    (body : NestedTheta.Term (Instruction Op) args [] sigs (Theta.BodyResults args))
    (childSound : ∀ i o, (Job.region body i (PUnit.unit : Locals m.Val [])).run m loops depth = some o →
      Returns m (.region body i (PUnit.unit : Locals m.Val [])) o)
    (input output : Tuple m.Val args)
    (evaluated : (Job.iteration body input).runWithin m loops depth remaining = some output) :
    Returns m (.iteration body input) output := by
  induction remaining generalizing input with
  | zero => cases evaluated
  | succ remaining ih =>
    let run (i : Tuple m.Val args) := evalBody m (dispatch m (invoke m loops depth)) loops
      (past := []) body i PUnit.unit
    simp only [Job.runWithin, NestedTheta.iterate] at evaluated
    cases reached : run input with
    | none =>
      rw [show evalBody m (dispatch m (invoke m loops depth)) loops (past := []) body input PUnit.unit =
        none from reached] at evaluated
      cases evaluated
    | some result =>
      cases result with
      | cons tag next =>
        rw [show evalBody m (dispatch m (invoke m loops depth)) loops (past := []) body input PUnit.unit =
          some (.cons tag next) from reached] at evaluated
        have ran := childSound input (.cons tag next) reached
        by_cases continues : (tag.selector.val == 1) = true
        · have rest : (Job.iteration body next).runWithin m loops depth remaining = some output := by
            simpa only [Job.runWithin, ite_eq_left continues] using evaluated
          exact .again ran continues (ih next rest)
        · have same : some next = some output := by
            simpa only [ite_eq_right continues] using evaluated
          have stopped : (tag.selector.val == 1) = false := by
            cases eq : (tag.selector.val == 1) <;> simp_all
          exact Option.some.inj same ▸ Returns.stop ran stopped

private theorem node_sound (m : Machine.{u, v, w} Op) (loops depth : Nat)
    (calls : CallSound m loops depth) (kind : NestedTheta.Kind (Instruction Op) args outs)
    (cs : Fin kind.arity → List (Ports (Ty V S))) (children : Bodies kind cs)
    (childSound : ∀ k i o, (Job.region (children k) i (PUnit.unit : Locals m.Val [])).run m loops depth = some o →
      Returns m (.region (children k) i (PUnit.unit : Locals m.Val [])) o)
    (input : Tuple m.Val args) (output : Tuple m.Val outs)
    (evaluated : (Job.node kind cs children input).run m loops depth = some output) :
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
  | theta =>
    let arm : Fin 1 := 0
    exact .theta (iteration_sound m loops depth loops (children arm) (childSound arm) input output evaluated)

private theorem region_sound (m : Machine.{u, v, w} Op) (loops depth : Nat)
    (calls : CallSound m loops depth) (term : NestedTheta.Term (Instruction Op) args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) (output : Tuple m.Val outs)
    (evaluated : (Job.region term entry locals).run m loops depth = some output) :
    Returns m (.region term entry locals) output := by
  induction term with
  | ret wires =>
    have eq : wires.read entry locals = output := Option.some.inj evaluated
    exact eq ▸ Returns.ret wires entry locals
  | bind node children rest childIH restIH =>
    let first := Job.node node.kind node.childSigs children (node.inputs.read entry locals)
    change (first.run m loops depth >>= fun value =>
      (Job.region rest entry (locals.snoc value)).run m loops depth) = some output at evaluated
    cases reached : first.run m loops depth with
    | none => rw [reached] at evaluated; cases evaluated
    | some value =>
      rw [reached] at evaluated
      exact .bind
        (node_sound m loops depth calls node.kind node.childSigs children
          (fun k i o => childIH k i PUnit.unit o) _ value reached)
        (restIH entry (locals.snoc value) output evaluated)

theorem call_sound (m : Machine.{u, v, w} Op) (loops depth : Nat) :
    ∀ {params results : Ports (Ty V S)} (callee : m.Val (.value (.function params results)))
      (input : Tuple m.Val params) (output : Tuple m.Val results),
      invoke m loops depth callee input = some output → Returns m (.call callee input) output := by
  induction depth with
  | zero =>
    intro _ _ _ _ _ empty
    cases empty
  | succ depth ih =>
    intro params results callee input output evaluated
    let closure := resolve m callee
    exact .call (region_sound m loops depth (fun callee input output => ih callee input output)
      closure.body.toTerm (Closure.enter Op closure input) PUnit.unit output evaluated)

private theorem complete_within (m : Machine.{u, v, w} Op) {job : Job m outs} {output : Tuple m.Val outs}
    (derivation : Returns m job output) :
    ∃ callLimit loopLimit, ∀ loops depth remaining,
      callLimit ≤ depth → loopLimit ≤ loops → loopLimit ≤ remaining →
      job.runWithin m loops depth remaining = some output := by
  induction derivation with
  | call body ih =>
    obtain ⟨callLimit, loopLimit, runs⟩ := ih
    refine ⟨callLimit + 1, loopLimit, fun loops depth remaining enough loopEnough enoughRemaining => ?_⟩
    cases depth with
    | zero => omega
    | succ depth => exact runs loops depth remaining (Nat.le_of_succ_le_succ enough) loopEnough enoughRemaining
  | ret wires input locals => exact ⟨0, 0, fun _ _ _ _ _ _ => rfl⟩
  | @bind args head outs past tail node children rest entry locals value output first more firstIH restIH =>
    obtain ⟨firstDepth, firstLoops, firstRun⟩ := firstIH
    obtain ⟨tailDepth, tailLoops, tailRun⟩ := restIH
    refine ⟨max firstDepth tailDepth, max firstLoops tailLoops, fun loops depth remaining calls budget steps => ?_⟩
    change ((Job.node node.kind node.childSigs children (node.inputs.read entry locals)).runWithin
      m loops depth loops >>= fun value =>
        (Job.region rest entry (locals.snoc value)).runWithin m loops depth remaining) = some output
    rw [firstRun loops depth loops (Nat.le_trans (Nat.le_max_left _ _) calls)
      (Nat.le_trans (Nat.le_max_left _ _) budget) (Nat.le_trans (Nat.le_max_left _ _) budget)]
    exact tailRun loops depth remaining (Nat.le_trans (Nat.le_max_right _ _) calls)
      (Nat.le_trans (Nat.le_max_right _ _) budget) (Nat.le_trans (Nat.le_max_right _ _) steps)
  | primitive opcode cs children input => exact ⟨0, 0, fun _ _ _ _ _ _ => rfl⟩
  | apply invocation ih => exact ih
  | gamma branch ih => exact ih
  | theta iterated ih =>
    obtain ⟨callLimit, loopLimit, runs⟩ := ih
    exact ⟨callLimit, loopLimit, fun loops depth _ enough budget _ =>
      runs loops depth loops enough budget budget⟩
  | @stop carried sigs body input output tag activation done ih =>
    obtain ⟨callLimit, loopLimit, runs⟩ := ih
    refine ⟨callLimit, max loopLimit 1, fun loops depth remaining calls budget steps => ?_⟩
    cases remaining with
    | zero => omega
    | succ remaining =>
      have ran : evalBody m (dispatch m (invoke m loops depth)) loops (past := []) body input PUnit.unit =
          some (.cons tag output) :=
        runs loops depth (remaining + 1) calls (Nat.le_trans (Nat.le_max_left _ _) budget)
          (Nat.le_trans (Nat.le_max_left _ _) steps)
      simp only [Job.runWithin, NestedTheta.iterate, ran]
      exact ite_eq_right (fun h => Bool.noConfusion (done.symm.trans h))
  | @again carried sigs body input next output tag activation continues later firstIH laterIH =>
    obtain ⟨firstDepth, firstLoops, firstRun⟩ := firstIH
    obtain ⟨tailDepth, tailLoops, tailRun⟩ := laterIH
    refine ⟨max firstDepth tailDepth, max firstLoops (tailLoops + 1), ?_⟩
    intro loops depth remaining calls budget steps
    cases remaining with
    | zero => omega
    | succ remaining =>
      have ran : evalBody m (dispatch m (invoke m loops depth)) loops (past := []) body input PUnit.unit =
          some (.cons tag next) :=
        firstRun loops depth (remaining + 1) (Nat.le_trans (Nat.le_max_left _ _) calls)
          (Nat.le_trans (Nat.le_max_left _ _) budget) (Nat.le_trans (Nat.le_max_left _ _) steps)
      simp only [Job.runWithin, NestedTheta.iterate, ran]
      have later := tailRun loops depth remaining (Nat.le_trans (Nat.le_max_right _ _) calls) (by omega) (by omega)
      simpa only [Job.runWithin, ite_eq_left continues] using later

theorem complete (m : Machine.{u, v, w} Op) {job : Job m outs} {output : Tuple m.Val outs}
    (derivation : Returns m job output) :
    ∃ callLimit loopLimit, ∀ loops depth, callLimit ≤ depth → loopLimit ≤ loops →
      job.run m loops depth = some output := by
  obtain ⟨calls, loops, runs⟩ := complete_within m derivation
  exact ⟨calls, loops, fun l d lc ll => runs l d l lc ll ll⟩

theorem call_iff (m : Machine.{u, v, w} Op) (callee : m.Val (.value (.function args outs)))
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    Returns m (.call callee input) output ↔ ∃ loops depth, invoke m loops depth callee input = some output := by
  constructor
  · intro returned
    obtain ⟨calls, loops, runs⟩ := complete m returned
    exact ⟨loops, calls, runs loops calls (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨loops, depth, evaluated⟩
    exact call_sound m loops depth callee input output evaluated

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Proofs

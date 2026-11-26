module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Captures
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Choice
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Regions
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Feedback
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

open Continuation.Partial
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ}
variable {context carry : Ports (Ty V S)} {fn : Function V S} {extra : Nat}
variable {ports : Fin (extra + 2) → Port context fn.port}

theorem family_related {capL capR : Tuple m.Val context} {inputL inputR : Tuple m.Val carry}
    (captures : TupleRelated m ids capL capR) (tag : Fin (extra + 2)) (inputs : TupleRelated m ids inputL inputR) :
    TupleRelated m ids (familyValue ports capL tag inputL) (familyValue ports capR tag inputR) :=
  prepend_related captures (.cons (.control tag) (.cons (captures.get (ports tag)) inputs))

theorem family_pair {capL capR : Tuple m.Val context}
    {left right : Tuple m.Val (context ++ FamilyArgs fn extra carry)}
    (related : TupleRelated m ids left right)
    (leftMember : ∃ tag input, left = familyValue ports capL tag input)
    (rightMember : ∃ tag input, right = familyValue ports capR tag input) :
    FamilyPair (ids := ids) ports capL capR left right := by
  obtain ⟨tagL, inputL, sameL⟩ := leftMember
  obtain ⟨tagR, inputR, sameR⟩ := rightMember
  rw [sameL, sameR] at related
  have tail := related_arguments related
  cases tail with
  | cons tag rest =>
    cases tag
    cases rest with
    | cons _ ordinary => exact ⟨tagL, inputL, inputR, ordinary, sameL, sameR⟩

private theorem get_parameter {params : Ports (Ty V S)} {t : Ty V S} (caps : Tuple m.Val context)
    (input : Tuple m.Val params) (port : Port params t) :
    (prependContext input caps).get (parameterPort context port) = input.get port := by
  induction caps with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem family_application_read
    (arguments : Wires (context ++ FamilyArgs fn extra carry) [] fn.args)
    (caps : Tuple m.Val context) (tag : Fin (extra + 2)) (input : Tuple m.Val carry) :
    (familyApplicationInputs fn arguments).read (familyValue ports caps tag input) PUnit.unit =
      .cons (caps.get (ports tag)) (arguments.read (familyValue ports caps tag input) PUnit.unit) :=
  congrArg (fun value => Tuple.cons value (arguments.read (familyValue ports caps tag input) PUnit.unit))
    (get_parameter caps (.cons (.control tag) (.cons (caps.get (ports tag)) input)) (.tail .head))

/-- Read the tag and callable forwarded by a completed γ, together with
the original family captures and the updated ordinary arguments. -/
theorem family_wires_read {params : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (selector : Origin (context ++ params) past (.control (extra + 2)))
    (ordinary : Wires (context ++ params) (past ++ [[fn.port]]) carry)
    (caps : Tuple m.Val context) (input : Tuple m.Val params) (locals : Locals m.Val past)
    (tag : Fin (extra + 2)) (selected : (Wires.read (.cons selector .nil) (prependContext input caps) locals).get .head = .control tag) :
    let scope := locals.snoc (.cons (caps.get (ports tag)) .nil)
    (familyWires fn selector ordinary).read (prependContext input caps) scope =
      familyValue ports caps tag (ordinary.read (prependContext input caps) scope) := by
  let entry := prependContext input caps
  let chosen := caps.get (ports tag)
  let scope := locals.snoc (.cons chosen .nil)
  have tagRead := (extended_origin_read selector entry locals (.cons chosen .nil)).trans selected
  have callRead := joined_origin_read entry locals chosen
  have project := read_projected caps input scope (NestedTheta.identityPorts context)
    (.cons (extendOrigin selector [fn.port]) (.cons (joinedOrigin (past := past) fn) ordinary))
  rw [project_identity] at project
  exact project.trans (congrArg (fun values => prependContext values caps)
    (congrArg₂ Tuple.cons tagRead (congrArg (fun value => Tuple.cons value (ordinary.read entry scope)) callRead)))

private theorem completed_binding {args head outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
    {node : NestedTheta.Node (Instruction Op) args past head} {children : Bodies node.kind node.childSigs}
    {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigs outs}
    {entry : Tuple m.Val args} {locals : Locals m.Val past} {store stopped : σ} {value : Tuple m.Val outs}
    (ran : Eval primitives (.region (.bind node children rest) entry locals) store (.returned value stopped)) :
    ∃ bound middle,
      Eval primitives (.node node.kind node.childSigs children (node.inputs.read entry locals)) store (.returned bound middle) ∧
      Eval primitives (.region rest entry (locals.snoc bound)) middle (.returned value stopped) := by
  cases ran with
  | bind first more => exact ⟨_, _, first, more⟩

private theorem return_read {args outs : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    {wires : Wires args past outs} {entry : Tuple m.Val args} {locals : Locals m.Val past} {store stopped : σ}
    {value : Tuple m.Val outs}
    (ran : Eval primitives (.region (.ret wires) entry locals) store (.returned value stopped)) :
    value = wires.read entry locals := by
  cases ran
  rfl

variable {arguments : Wires (context ++ FamilyArgs fn extra carry) [] fn.args}
variable {select : Origin (context ++ FamilyArgs fn extra carry) [fn.results] (.control (extra + 2))}
variable {feedback : Origin (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]] (.control 2)}
variable {ordinary : Wires (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]] carry}

private theorem family_returned (caps : Tuple m.Val context) (tag : Fin (extra + 2)) (input : Tuple m.Val carry)
    {store stopped : σ} {exit : m.Val (.control 2)} {value : Tuple m.Val (context ++ FamilyArgs fn extra carry)}
    (ran : Eval primitives (.region (familyBody fn ports arguments select feedback ordinary)
      (familyValue ports caps tag input) PUnit.unit) store (.returned (.cons exit value) stopped)) :
    ∃ next args, value = familyValue ports caps next args := by
  obtain ⟨result, _, _, tail⟩ := completed_binding ran
  obtain ⟨chosen, _, chose, returned⟩ := completed_binding tail
  let params := Tuple.cons (.control tag) (.cons (caps.get (ports tag)) input)
  let locals := Locals.snoc (past := []) PUnit.unit result
  obtain ⟨next, guard, same⟩ := chooser_returned select ports caps params locals chose
  subst chosen
  have read := congrArg (fun | .cons _ carried => carried) (return_read returned)
  exact ⟨next, _, read.trans (family_wires_read (ports := ports) select ordinary caps params locals next guard)⟩

/-- Recover membership at any actual restart by inverting successful
activations. In particular the next member may differ from the first. -/
private theorem family_restarts (caps : Tuple m.Val context)
    {first current : Tuple m.Val (context ++ FamilyArgs fn extra carry) × σ}
    (start : ∃ tag input, first.1 = familyValue ports caps tag input)
    (completed : ReflTransGen (Feedback.Iteration primitives (familyBody fn ports arguments select feedback ordinary)) first current) :
    ∃ tag input, current.1 = familyValue ports caps tag input := by
  induction completed with
  | refl => exact start
  | tail _ step ih =>
    obtain ⟨tag, input, same⟩ := ih
    obtain ⟨_, ran, _⟩ := step
    rw [same] at ran
    exact family_returned caps tag input ran

/-- Any finite sequence of paired actual restarts preserves admissible
membership, with a common index that may change at each transition. -/
theorem family_pair_restarts {capL capR : Tuple m.Val context}
    {first current : SingleTheta.Carries m ids σ (context ++ FamilyArgs fn extra carry)}
    (start : FamilyPair (ids := ids) ports capL capR first.left first.right)
    (completed : ReflTransGen (IterationPair primitives (familyBody fn ports arguments select feedback ordinary)
      (familyBody fn ports arguments select feedback ordinary)) first current) :
    FamilyPair (ids := ids) ports capL capR current.left current.right := by
  obtain ⟨tag, inputL, inputR, _, sameL, sameR⟩ := start
  exact family_pair current.related
    (family_restarts capL ⟨tag, inputL, sameL⟩ (left_completed completed))
    (family_restarts capR ⟨tag, inputR, sameR⟩ (right_completed completed))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

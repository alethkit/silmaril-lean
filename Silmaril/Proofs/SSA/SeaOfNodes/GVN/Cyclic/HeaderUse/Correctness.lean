module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse
open Activation (View Inputs InputsAgree sourceWire headerRead)
open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires)
open Elimination (inFinal operandScope)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {out sort : ValueSort Data} {t : Ty Data} {flow : Dataflow Op args past sigs}

private theorem setOperand_read {ports : List (Ty Data)} (m : Model.{u,v,w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (use : Port ports t) (replacement : Origin args past t) (wires : Wires args past ports)
    (same : Diamond.read m (wires.get use) entry locals = Diamond.read m replacement entry locals) :
    (setOperand use replacement wires).read entry locals = wires.read entry locals := by
  induction use with
  | head =>
    cases wires with
    | cons _ rest => exact congrArg (fun value => Tuple.cons value (Wires.read rest entry locals)) same.symm
  | tail _ ih =>
    cases wires with
    | cons head tail =>
      exact congrArg (fun rest => Tuple.cons (Diamond.read m head entry locals) rest) (ih replacement tail same)

theorem replace_eval (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args)
    (consumer : Producer flow out) (use : Port (dataPorts consumer.key.ins) t)
    (replacement : Origin args (operandScope consumer) t) (locals : Locals (Val m.value) past)
    (same : let final := flow.eval m entry locals
      Diamond.read m (inFinal consumer (operandAt consumer use)) entry final =
        Diamond.read m (inFinal consumer replacement) entry final) :
    (replaceAt consumer use replacement).eval m entry locals = flow.eval m entry locals := by
  induction consumer with
  | @here scope _ _ output opcode operands rest =>
    let next : Tuple (Val m.value) [.value output] := .cons (m.run opcode (operands.read entry locals)) .nil
    have lift (wire : Origin args scope t) :
        Diamond.read m (keepOrigin rest (weaken [.value output] wire)) entry
          (rest.eval m entry (locals.snoc next)) = Diamond.read m wire entry locals :=
      (read_keepOrigin rest _ m entry _).trans (read_weaken wire m entry locals next)
    have localEq := (lift (operands.get use)).symm.trans (same.trans (lift replacement))
    have reads := setOperand_read m entry locals use replacement operands localEq
    exact congrArg (fun values => rest.eval m entry (locals.snoc (.cons (m.run opcode values) .nil))) reads
  | later _ ih =>
    exact ih use replacement _ same

private theorem origin_eq_of_address (a b : Origin args past t) (same : a.address = b.address) : a = b :=
  congrArg (fun (wires : Wires args past [t]) => wires.get .head)
    (Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective (.cons a .nil) (.cons b .nil)
      (congrArg (fun address => [address]) same))

variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {n : Nat} {sorts : Fin n → ValueSort Data} {consumerOut : ValueSort Data}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable {g : Cyclic.Graph Op inputs sorts} {p : Partition n}
variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

variable (view : View g loop) (consumer : Producer loop.header consumerOut)
variable (use : Port (dataPorts consumer.key.ins) (.value sort))
variable (original representative : Source inputs sorts sort)
variable (prefixWire : Origin (Loop.headerPorts inputs carried) (operandScope consumer) (.value sort))

theorem check_correct :
    check view p consumer use original representative prefixWire = true ↔
      Stable g p ∧ original.address.relabel p = representative.address.relabel p ∧
        inFinal consumer (operandAt consumer use) = sourceWire view.site original ∧
        inFinal consumer prefixWire = sourceWire view.site representative := by
  simp only [check, Bool.and_eq_true_iff, decide_eq_true_eq, checkStable_eq_true_iff, and_assoc]
  constructor
  · rintro ⟨stable, key, old, new⟩
    exact ⟨stable, key, origin_eq_of_address _ _ old, origin_eq_of_address _ _ new⟩
  · rintro ⟨stable, key, old, new⟩
    exact ⟨stable, key, congrArg Origin.address old, congrArg Origin.address new⟩

variable {rewritten : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable (accepted : redirect? view p consumer use original representative prefixWire = some rewritten)

include accepted in
theorem redirect_initial (m : Model.{u,v,w} Op) (input : Inputs m inputs) :
    rewritten.initial m input = loop.initial m input := by
  unfold redirect? at accepted
  split at accepted
  · obtain rfl := Option.some.inj accepted
    rfl
  · cases accepted

include accepted in
theorem redirect_step (m : Model.{u,v,w} Op) (input : Inputs m inputs) (old : Inputs m carried)
    (invariant : view.LatchesAgree p m old old) :
    headerRead rewritten m input old rewritten.predicate = headerRead loop m input old loop.predicate ∧
      rewritten.step m input old = loop.step m input old ∧
      ∀ next, rewritten.step m input old = .inr next → view.LatchesAgree p m next next := by
  unfold redirect? at accepted
  split at accepted
  · obtain rfl := Option.some.inj accepted
    obtain ⟨stable, key, oldWire, newWire⟩ :=
      (check_correct view consumer use original representative prefixWire).mp ‹_›
    have fixed : InputsAgree m input input := fun _ => rfl
    have classes := view.header_agrees stable fixed invariant
    have valueEq := view.read_agrees fixed classes original representative key
    rw [← oldWire, ← newWire] at valueEq
    let args := Loop.appendTuple old input
    have headerEq := replace_eval m args consumer use prefixWire PUnit.unit valueEq
    have guardEq : headerRead
        ({ loop with header := replaceAt consumer use prefixWire } :
          Loop.Graph Op inputs carried entrySigs headerSigs out)
        m input old loop.predicate = headerRead loop m input old loop.predicate := by
      exact congrArg (Diamond.read m loop.predicate args) headerEq
    have stepEq : ({ loop with header := replaceAt consumer use prefixWire } :
        Loop.Graph Op inputs carried entrySigs headerSigs out).step m input old =
          loop.step m input old := by
      simp only [Loop.Graph.step, Loop.Graph.latch, args, headerEq]
    refine ⟨guardEq, stepEq, ?_⟩
    intro next taken
    rw [stepEq] at taken
    have outcome := (view.step_agrees stable fixed invariant).2
    rw [taken] at outcome
    exact outcome
  · cases accepted

include accepted in
theorem redirect_eval (m : Model.{u,v,w} Op) (input : Inputs m inputs) (budget : Nat) :
    rewritten.evalBackedges m budget input = loop.evalBackedges m budget input := by
  have checked : check view p consumer use original representative prefixWire = true := by
    unfold redirect? at accepted
    split at accepted
    · assumption
    · cases accepted
  have stable := ((check_correct view consumer use original representative prefixWire).mp checked).1
  have fixed : InputsAgree m input input := fun _ => rfl
  have evalFromEq (fuel : Nat) (old : Inputs m carried) (invariant : view.LatchesAgree p m old old) :
      rewritten.evalFrom m input fuel old = loop.evalFrom m input fuel old := by
    induction fuel generalizing old with
    | zero =>
      have step := (redirect_step view consumer use original representative prefixWire accepted
        m input old invariant).2.1
      simp only [Loop.Graph.evalFrom, step]
    | succ fuel ih =>
      have step := (redirect_step view consumer use original representative prefixWire accepted
        m input old invariant).2
      simp only [Loop.Graph.evalFrom, step.1]
      cases taken : loop.step m input old with
      | inl _ => rfl
      | inr next =>
        exact ih next (step.2 next (step.1.trans taken))
  unfold Loop.Graph.evalBackedges
  rw [redirect_initial view consumer use original representative prefixWire accepted]
  exact evalFromEq budget _ (view.initial_agrees stable fixed)

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse

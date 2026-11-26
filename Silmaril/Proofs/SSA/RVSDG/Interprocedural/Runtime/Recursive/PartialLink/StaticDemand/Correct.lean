module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Wiring

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

open NestedTheta.Liveness (Demand DemandPlan selectWires definedAt transfer sweep mem_sweep_iff)
open NestedTheta.Liveness.Demand.Proofs (ScopeAgrees valueAt read_all read_selected scope_snoc)
open Continuation (Stack)
open Continuation.Partial (Config Site)
open Continuation.Partial.Executable (Actions next? observe runFor observe_returned observe_blocked)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {entry results final : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

/-- The demanded ports after prepending captures use exactly the two ranges
in the application transfer. -/
private theorem prepend_agrees {Ty : Type u} {F : Ty → Type w} {context params : Ports Ty}
    (wanted : Nat → Prop) (capsL capsR : Tuple F context) (argsL argsR : Tuple F params)
    (cap : ∀ {ty} (p : Port context ty), wanted p.index → capsL.get p = capsR.get p)
    (arg : ∀ {ty} (p : Port params ty), wanted (context.length + p.index) → argsL.get p = argsR.get p) :
    ∀ {ty} (p : Port (context ++ params) ty), wanted p.index →
      (prependContext argsL capsL).get p = (prependContext argsR capsR).get p := by
  induction capsL generalizing wanted with
  | nil =>
    cases capsR
    intro ty p live
    exact arg p (by simpa only [List.length_nil, Nat.zero_add] using live)
  | cons x xs ih =>
    cases capsR with
    | cons y ys =>
      intro ty p live
      cases p with
      | head => exact cap .head live
      | tail p =>
        apply ih (fun i => wanted (i + 1)) ys
        · exact fun p live => cap (.tail p) live
        · intro ty p live
          exact arg p (by simpa only [List.length_cons, Nat.succ_add] using live)
        · exact live

private theorem apply_agrees {params context : Ports (Ty V S)} (live : List Address)
    (captures : Wires entry [] context) (arguments : Wires entry past params)
    {entryL entryR : Tuple m.Val entry} {localsL localsR : Locals m.Val past}
    (agree : ScopeAgrees (applyReads live captures arguments) entryL entryR localsL localsR) :
    ScopeAgrees (scope := []) live
      (prependContext (arguments.read entryL localsL) (captures.read entryL PUnit.unit))
      (prependContext (arguments.read entryR localsR) (captures.read entryR PUnit.unit))
      PUnit.unit PUnit.unit := by
  intro ty origin needed
  cases origin with
  | output i _ => exact i.elim0
  | arg p =>
    apply prepend_agrees (fun i => Address.arg i ∈ live)
    · intro ty p present
      apply read_selected (fun _ i => live.contains (.arg i)) captures _ p (List.contains_iff_mem.2 present)
      intro ty origin selected
      cases origin with
      | output i _ => exact i.elim0
      | arg q => exact agree (.arg q) (List.mem_append_left _ selected)
    · intro ty p present
      exact read_selected (fun _ i => live.contains (.arg (context.length + i))) arguments
        (fun origin selected => agree origin (List.mem_append_right _ selected)) p (List.contains_iff_mem.2 present)
    · exact needed

private theorem split_live {reads : List Address} {next : DemandPlan} {left right : Tuple m.Val entry}
    {localsL localsR : Locals m.Val past}
    (agree : ScopeAgrees (next.prepend past.length reads).live left right localsL localsR) :
    ScopeAgrees reads left right localsL localsR ∧
    ScopeAgrees (next.live.filter (fun a => !definedAt past.length a)) left right localsL localsR :=
  ⟨fun _ live => agree _ (List.mem_append_left _ live), fun _ live => agree _ (List.mem_append_right _ live)⟩

private def ResumeAgrees (actions : Actions m σ) (observed wanted : Demand)
    (left right : Stack m results final) : Prop :=
  ∀ (outL outR : Tuple m.Val results) (store : σ), wanted.Agrees outL outR →
    Matches actions observed ⟨.returned outL left, store⟩ ⟨.returned outR right, store⟩

private theorem output_observed {ty : Ty V S} {pc p : Nat} {plan : DemandPlan}
    (live : Address.output pc p ∈ plan.live) : (resultDemand pc plan).observes ty p = true := by
  cases ty with
  | state => rfl
  | control | value => exact List.contains_iff_mem.2 live

private theorem region (actions : Actions m σ) (observed : Demand) (code : Code Op entry past sigs results) :
    ∀ (wanted : Demand) (inputL inputR : Tuple m.Val entry) (localsL localsR : Locals m.Val past)
      (left right : Stack m results final) (store : σ),
      code.Resolved inputL → code.Resolved inputR →
      ScopeAgrees (code.plan wanted).live inputL inputR localsL localsR →
      ResumeAgrees actions observed wanted left right →
      Matches actions observed
        ⟨.eval (.region code.term inputL localsL) left, store⟩
        ⟨.eval (.region code.term inputR localsR) right, store⟩ := by
  induction code with
  | ret wires =>
    intro wanted inputL inputR localsL localsR left right store _ _ agree resume
    apply Matches.step rfl rfl
    apply resume
    exact fun p requested => read_selected wanted.observes wires
      (fun edge live => agree edge (List.mem_append_left _ live)) p requested
  | @primitive entry results ins outs past sigs opcode operands rest ih =>
    intro wanted inputL inputR localsL localsR left right store resolvedL resolvedR agree resume
    obtain ⟨reads, old⟩ := split_live agree
    let frameL : Stack m outs final := .resume rest.term inputL localsL left
    let frameR : Stack m outs final := .resume rest.term inputR localsR right
    have after : ResumeAgrees actions observed (resultDemand past.length (rest.plan wanted)) frameL frameR := by
      intro outL outR middle demanded
      apply Matches.step rfl rfl
      exact ih wanted inputL inputR _ _ left right middle resolvedL resolvedR
        (scope_snoc old (fun p live => demanded p (output_observed live))) resume
    let site : Site m := ⟨ins, outs, opcode, fun i => i.elim0, fun i => i.elim0, operands.read inputL localsL⟩
    have operands_eq := read_all operands reads
    have advanceL : next? actions (⟨.eval (.region (.primitive opcode operands rest : Code Op entry past _ results).term
        inputL localsL) left, store⟩ : Config m σ final) = some ⟨.eval site.job frameL, store⟩ := rfl
    have advanceR : next? actions (⟨.eval (.region (.primitive opcode operands rest : Code Op entry past _ results).term
        inputR localsR) right, store⟩ : Config m σ final) = some ⟨.eval site.job frameR, store⟩ := by
      change some (⟨.eval { site with input := operands.read inputR localsR }.job frameR, store⟩ :
        Config m σ final) = _
      rw [← operands_eq]
    apply Matches.step advanceL advanceR
    cases tried : (actions.step site.opcode site.input).run store with
    | none => exact .blocked tried (fun value middle => after value value middle (fun _ _ => rfl))
    | some outcome =>
      obtain ⟨value, middle⟩ := outcome
      have step (frame : Stack m outs final) :
          next? actions ⟨.eval site.job frame, store⟩ = some ⟨.returned value frame, middle⟩ := by
        change ((actions.step site.opcode site.input).run store).map
          (fun (v, s) => (⟨.returned v frame, s⟩ : Config m σ final)) = _
        rw [tried]
        rfl
      exact .step (step frameL) (step frameR) (after value value middle (fun _ _ => rfl))
  | @apply entry results context fn past sigs bodySigs target captures body arguments rest ihBody ihRest =>
    intro wanted inputL inputR localsL localsR left right store resolvedL resolvedR agree resume
    obtain ⟨reads, old⟩ := split_live agree
    obtain ⟨targetL, bodyL, restL⟩ := resolvedL
    obtain ⟨targetR, bodyR, restR⟩ := resolvedR
    let frameL : Stack m fn.results final := .resume rest.term inputL localsL left
    let frameR : Stack m fn.results final := .resume rest.term inputR localsR right
    let needed := resultDemand past.length (rest.plan wanted)
    have after : ResumeAgrees actions observed needed frameL frameR := by
      intro outL outR middle demanded
      apply Matches.step rfl rfl
      exact ihRest wanted inputL inputR _ _ left right middle restL restR
        (scope_snoc old (fun p live => demanded p (output_observed live))) resume
    let capL := captures.read inputL PUnit.unit
    let capR := captures.read inputR PUnit.unit
    let argL := arguments.read inputL localsL
    let argR := arguments.read inputR localsR
    have openBody (f : m.Val fn.port) (capture : Tuple m.Val context) (arg : Tuple m.Val fn.args)
        (frame : Stack m fn.results final) (resolved : f = .closure capture body.term.toGraph) :
        next? actions ⟨.eval (.call f arg) frame, store⟩ =
          some ⟨.eval (.region body.term (prependContext arg capture) PUnit.unit) frame, store⟩ := by
      subst f
      change some (⟨.eval (.region body.term.toGraph.toTerm (prependContext arg capture) PUnit.unit) frame, store⟩ :
        Config m σ final) = _
      rw [NestedTheta.Term.toTerm_toGraph]
    apply Matches.step rfl rfl
    apply Matches.step rfl rfl
    apply Matches.step (openBody _ capL argL frameL targetL) (openBody _ capR argR frameR targetR)
    exact ihBody needed _ _ PUnit.unit PUnit.unit frameL frameR store (bodyL argL) (bodyR argR)
      (apply_agrees _ captures arguments reads) after

private theorem plan_live (code : Code Op entry past sigs results) (demand : Demand) :
    (code.plan demand).live = sweep (code.plan demand).reads past.length := by
  induction code with
  | ret => rfl
  | primitive _ _ _ ih =>
    simp only [Code.plan, DemandPlan.prepend, sweep, ih, List.length_append,
      List.length_cons, List.length_nil]
  | apply _ _ _ _ _ _ ih =>
    simp only [Code.plan, DemandPlan.prepend, sweep, ih, List.length_append,
      List.length_cons, List.length_nil]

theorem mem_liveIn_iff (code : Code Op entry [] sigs results) (demand : Demand) (a : Address) :
    a ∈ code.liveIn demand ↔ a ∈ (code.liveness demand).mayOut 0 := by
  simpa only [Code.liveIn, List.mem_eraseDups, plan_live, List.length_nil,
    Code.liveness, List.drop_zero] using mem_sweep_iff (code.plan demand).reads 0 a

theorem settles {actions : Actions m σ} {demand : Demand} {left right : Config m σ results}
    (checked : Matches actions demand left right) :
    ∃ fuel, EndpointsAgree actions demand
      (observe actions (runFor actions fuel left)) (observe actions (runFor actions fuel right)) := by
  induction checked with
  | returned agree =>
    exact ⟨0, by rw [runFor, runFor, observe_returned.2 rfl, observe_returned.2 rfl]; exact .returned agree⟩
  | step stepL stepR _ ih =>
    obtain ⟨fuel, related⟩ := ih
    exact ⟨fuel + 1, by simpa only [runFor, stepL, stepR] using related⟩
  | @blocked site left right store undefined resume _ =>
    refine ⟨0, ?_⟩
    have seen (frame : Stack m site.outs results) :
        observe actions ⟨.eval site.job frame, store⟩ = .blocked ⟨site, frame⟩ store := by
      apply observe_blocked.2
      refine ⟨rfl, rfl, ?_⟩
      change Part.ofOption ((actions.step site.opcode site.input).run store) = Part.none
      rw [undefined]
      rfl
    rw [runFor, runFor, seen, seen]
    exact .blocked resume

theorem matches_calls {fn : Function V S} {context : Ports (Ty V S)}
    (code : Code Op (context ++ fn.args) [] sigs fn.results)
    (actions : Actions m σ) (demand : Demand) (fL fR : m.Val fn.port)
    (capsL capsR : Tuple m.Val context) (argsL argsR : Tuple m.Val fn.args) (store : σ)
    (closureL : fL = .closure capsL code.term.toGraph)
    (closureR : fR = .closure capsR code.term.toGraph)
    (resolvedL : code.Resolved (prependContext argsL capsL))
    (resolvedR : code.Resolved (prependContext argsR capsR))
    (agree : code.AgreesOnInputs demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    Matches actions demand
      ⟨Continuation.start (.call fL argsL), store⟩
      ⟨Continuation.start (.call fR argsR), store⟩ := by
  subst fL fR
  have entry_step (caps : Tuple m.Val context) (args : Tuple m.Val fn.args) :
      next? actions ⟨Continuation.start (.call (.closure caps code.term.toGraph) args), store⟩ =
        some ⟨.eval (.region code.term (prependContext args caps) PUnit.unit) .halt, store⟩ := by
    change some (⟨.eval (.region code.term.toGraph.toTerm (prependContext args caps) PUnit.unit) .halt, store⟩ :
      Config m σ fn.results) = _
    rw [NestedTheta.Term.toTerm_toGraph]
  apply Matches.step (entry_step capsL argsL) (entry_step capsR argsR)
  apply region actions demand code demand _ _ PUnit.unit PUnit.unit .halt .halt store resolvedL resolvedR
  · intro ty source live
    cases source with
    | output i _ => exact i.elim0
    | arg p => exact agree p (List.mem_eraseDups.2 live)
  · exact fun _ _ _ equal => .returned equal

theorem linked_runs_agree {fn : Function V S} {context : Ports (Ty V S)}
    {imports exports : Ports (Ty V S)} {moduleSigs : List (Ports (Ty V S))}
    (code : Code Op (context ++ fn.args) [] sigs fn.results)
    (actions : Actions m σ) (demand : Demand) (graph : Omega Op imports exports moduleSigs)
    (unitId : Nat) (port : Port exports fn.port)
    (inputsL inputsR : Tuple m.Val imports) (argsL argsR : Tuple m.Val fn.args) (initial : σ)
    {exportsL exportsR : Tuple m.Val exports} {middle : σ}
    {capsL capsR : Tuple m.Val context}
    (linkedL : Executable.link actions unitId graph inputsL initial = .linked exportsL middle)
    (linkedR : Executable.link actions unitId graph inputsR initial = .linked exportsR middle)
    (closureL : exportsL.get port = .closure capsL code.term.toGraph)
    (closureR : exportsR.get port = .closure capsR code.term.toGraph)
    (resolvedL : code.Resolved (prependContext argsL capsL))
    (resolvedR : code.Resolved (prependContext argsR capsR))
    (agree : code.AgreesOnInputs demand (prependContext argsL capsL) (prependContext argsR capsR)) :
    ∃ fuel observedL observedR,
      Executable.run actions fuel unitId graph inputsL port argsL initial = .ok observedL ∧
      Executable.run actions fuel unitId graph inputsR port argsR initial = .ok observedR ∧
      EndpointsAgree actions demand observedL observedR := by
  obtain ⟨fuel, related⟩ := settles (matches_calls code actions demand _ _ capsL capsR argsL argsR middle
    closureL closureR resolvedL resolvedR agree)
  refine ⟨fuel, _, _, ?_, ?_, related⟩
  · simp only [Executable.run, Executable.start, linkedL, Except.map]
    rfl
  · simp only [Executable.run, Executable.start, linkedR, Except.map]
    rfl

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

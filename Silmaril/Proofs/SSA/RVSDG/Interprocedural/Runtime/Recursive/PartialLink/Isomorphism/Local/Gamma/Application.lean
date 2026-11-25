module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Feedback
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Regions
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Environments
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

open Continuation.Partial
open Continuation.Descent (Pending)
open Isomorphism.Proofs (LocalsRelated read_same)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {args outs captured : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {fn : Function V S}

private theorem application_reaches {entry : Tuple m.Val args} {past : List (Ports (Ty V S))} {locals : Locals m.Val past}
    {inputs : Wires args past (fn.port :: fn.args)}
    {callee : m.Val fn.port} {arguments : Tuple m.Val fn.args} {store : σ}
    {target : Feedback.Restart m σ} {pending : Pending m target.carried fn.results}
    (selected : inputs.read entry locals = .cons callee arguments)
    (ran : Feedback.Reaches primitives (.call callee arguments) store target pending) :
    Feedback.Reaches primitives (.node (applicationVertex fn inputs).kind (applicationVertex fn inputs).childSigs
      (fun i => i.elim0) (inputs.read entry locals)) store target pending :=
  selected.symm ▸ Feedback.Reaches.apply (fn := fn) (cs := fun _ => []) (children := fun i => i.elim0) ran

private theorem application_then
    {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
    {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
    {tailL tailR : List (Ports (Ty V S))}
    {suffixL : Term Op args [fn.results] tailL outs} {suffixR : Term Op args [fn.results] tailR outs}
    (respects : ActionsRespect primitives ids) (inputs : Wires args [] (fn.port :: fn.args))
    (suffix : Local.Schedule Op .identity suffixL suffixR)
    {entryL entryR : Tuple m.Val args} (entries : TupleRelated m ids entryL entryR)
    {captL captR : Tuple m.Val captured} {argsL argsR : Tuple m.Val fn.args} {store : σ}
    (selectL : inputs.read entryL PUnit.unit = .cons (.closure captL left.toGraph) argsL)
    (selectR : inputs.read entryR PUnit.unit = .cons (.closure captR right.toGraph) argsR)
    (observed : RegionPair primitives ids mapping left right
      (prependContext argsL captL) (prependContext argsR captR) store) :
    RegionPair primitives ids mapping (applicationThen fn inputs suffixL) (applicationThen fn inputs suffixR)
      entryL entryR store := by
  have actualL := open_lambda left captL argsL
  have actualR := open_lambda right captR argsR
  cases observed with
  | @returned _ _ middle values ranL ranR =>
    have calledL := Eval.call (actualL.symm ▸ ranL)
    have calledR := Eval.call (actualR.symm ▸ ranR)
    obtain ⟨_, _, resumed⟩ := Local.suffix_evaluate suffix respects entries values middle
    cases resumed with
    | returned results restL restR =>
      exact .returned results (.bind (node := applicationVertex fn inputs) (application_eval selectL calledL) restL)
        (.bind (node := applicationVertex fn inputs) (application_eval selectR calledR) restR)
    | blocked location sites restL restR =>
      exact .blocked (.afterApplication inputs suffixL suffixR selectL selectR calledL calledR location sites restL restR)
  | blocked stopped =>
    exact .blocked (.applicationThen inputs suffixL suffixR selectL selectR stopped)
  | productive run =>
    refine .productive (productive_map run ?_ ?_)
    · intro target pending reached
      exact ⟨.bind (past := []) (embed suffixL) entryL PUnit.unit pending,
        .inside (node := applicationVertex fn inputs)
          (application_reaches selectL (.call (actualL.symm ▸ reached)))⟩
    · intro target pending reached
      exact ⟨.bind (past := []) (embed suffixR) entryR PUnit.unit pending,
        .inside (node := applicationVertex fn inputs)
          (application_reaches selectR (.call (actualR.symm ▸ reached)))⟩

private theorem fixed_wires {ports : Ports (Ty V S)} (wires : Wires args [fn.results] ports) :
    wires.addresses.map (Address.rename Renaming.identity.vertices) = wires.addresses := by
  induction wires with
  | nil => rfl
  | cons origin _ ih =>
    cases origin <;> simp [Wires.addresses, Origin.address, Address.rename, Renaming.vertices,
      show List.map (Address.rename id) (Wires.addresses _) = _ from ih]

theorem application
    {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
    {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
    (code : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (inputs : Wires args [] (fn.port :: fn.args)) (outputs : Wires args [fn.results] outs)
    {entryL entryR : Tuple m.Val args} (entries : TupleRelated m ids entryL entryR)
    {captL captR : Tuple m.Val captured} (captures : TupleRelated m ids captL captR)
    {argsL argsR : Tuple m.Val fn.args} (arguments : TupleRelated m ids argsL argsR)
    (selectL : inputs.read entryL PUnit.unit = .cons (.closure captL left.toGraph) argsL)
    (selectR : inputs.read entryR PUnit.unit = .cons (.closure captR right.toGraph) argsR) (store : σ) :
    RegionPair primitives ids mapping (applicationCode fn inputs outputs) (applicationCode fn inputs outputs)
      entryL entryR store :=
  application_then respects inputs (.ret outputs outputs (fixed_wires outputs)) entries selectL selectR
    (regions code respects (prepend_related captures arguments) store)

/-- A static caller reads its function from its first captured port. -/
theorem captured_application
    {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
    {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
    (code : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (arguments : Wires (fn.port :: args) [] fn.args) (outputs : Wires (fn.port :: args) [fn.results] outs)
    {tailL tailR : Tuple m.Val args} (tails : TupleRelated m ids tailL tailR)
    {captL captR : Tuple m.Val captured} (captures : TupleRelated m ids captL captR)
    (iso : NestedTheta.Graph.Isomorphic (Instruction Op) left.toGraph right.toGraph) (store : σ) :
    RegionPair primitives ids mapping (applicationCode fn (.cons (.arg .head) arguments) outputs)
      (applicationCode fn (.cons (.arg .head) arguments) outputs)
      (.cons (.closure captL left.toGraph) tailL) (.cons (.closure captR right.toGraph) tailR) store := by
  have entries := TupleRelated.cons (ValueRelated.closure captures iso) tails
  exact application code respects (.cons (.arg .head) arguments) outputs entries captures
    (read_same entries LocalsRelated.empty arguments) rfl rfl store

theorem call_plan_regions {rank : Nat} {context params : Ports (Ty V S)}
    {capturesL capturesR : Tuple m.Val context}
    {left : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsL outs}
    {right : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsR outs}
    (plan : CallPlan m ids mapping rank capturesL capturesR left right)
    (respects : ActionsRespect primitives ids) :
    TupleRelated m ids capturesL capturesR ∧
      ∀ {argsL argsR : Tuple m.Val params}, TupleRelated m ids argsL argsR → ∀ store,
        RegionPair primitives ids mapping left right (prependContext argsL capturesL) (prependContext argsR capturesR) store := by
  induction plan with
  | body captures code =>
    exact ⟨captures, fun arguments store => regions code respects (prepend_related captures arguments) store⟩
  | application _ iso captures arguments suffix ih =>
    have paired := TupleRelated.cons (ValueRelated.closure ih.1 iso) captures
    refine ⟨paired, ?_⟩
    intro argsL argsR supplied store
    have entries := prepend_related paired supplied
    have operands := read_same entries LocalsRelated.empty arguments
    exact application_then respects (.cons (.arg .head) arguments) suffix entries rfl rfl (ih.2 operands store)

private theorem get_capture {t : Ty V S} {context params : Ports (Ty V S)}
    (port : Port context t) (captures : Tuple m.Val context) (arguments : Tuple m.Val params) :
    (prependContext arguments captures).get (capturePort port) = captures.get port := by
  induction port with
  | head => cases captures; rfl
  | tail port ih => cases captures with | cons _ rest => exact ih rest

private theorem project_related {context childContext : Ports (Ty V S)} {capL capR : Tuple m.Val context}
    (captured : TupleRelated m ids capL capR) (ports : Tuple (Port context) childContext) :
    TupleRelated m ids (projectCaptures capL ports) (projectCaptures capR ports) := by
  induction ports with
  | nil => exact .nil
  | cons port _ ih => exact .cons (captured.get port) ih

private theorem read_projected {context params childContext childArgs : Ports (Ty V S)}
    {past : List (Ports (Ty V S))} (captures : Tuple m.Val context) (paramsIn : Tuple m.Val params)
    (locals : Locals m.Val past) (ports : Tuple (Port context) childContext)
    (arguments : Wires (context ++ params) past childArgs) :
    Wires.read (prependContext arguments (ports.map (fun _ port => .arg (capturePort port))))
        (prependContext paramsIn captures) locals =
      prependContext (arguments.read (prependContext paramsIn captures) locals) (projectCaptures captures ports) := by
  induction ports with
  | nil => rfl
  | cons port rest ih =>
    exact congrArg₂ Tuple.cons (get_capture port captures paramsIn) ih

private theorem read_arm_input {context params childContext childArgs : Ports (Ty V S)}
    {past : List (Ports (Ty V S))} {extra : Nat} {tag : Fin (extra + 2)}
    (captures : Tuple m.Val context) (paramsIn : Tuple m.Val params) (locals : Locals m.Val past)
    (selector : Origin (context ++ params) past (.control (extra + 2)))
    (ports : Tuple (Port context) childContext) (arguments : Wires (context ++ params) past childArgs)
    (selected : ((Wires.read (.cons selector .nil) (prependContext paramsIn captures) locals).get .head) = .control tag) :
    (armInputs selector ports arguments).read (prependContext paramsIn captures) locals =
      .cons (.control tag)
        (prependContext (arguments.read (prependContext paramsIn captures) locals) (projectCaptures captures ports)) :=
  congrArg₂ Tuple.cons selected (read_projected captures paramsIn locals ports arguments)

private theorem bind_pair
    {past : List (Ports (Ty V S))} {tailL tailR : List (Ports (Ty V S))}
    {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
    {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
    {restL : NestedTheta.Term (Instruction Op) args (past ++ [fn.results]) tailL outs}
    {restR : NestedTheta.Term (Instruction Op) args (past ++ [fn.results]) tailR outs}
    {entryL entryR : Tuple m.Val args} {localsL localsR : Locals m.Val past}
    {capL capR : Tuple m.Val captured} {argsL argsR : Tuple m.Val fn.args} {store : σ}
    (inputs : Wires args past (fn.port :: fn.args))
    (selectL : inputs.read entryL localsL = .cons (.closure capL left.toGraph) argsL)
    (selectR : inputs.read entryR localsR = .cons (.closure capR right.toGraph) argsR)
    (callee : RegionPair primitives ids (mapping.child past.length 0) left right
      (prependContext argsL capL) (prependContext argsR capR) store)
    (resume : ∀ {valueL valueR : Tuple m.Val fn.results}, TupleRelated m ids valueL valueR → ∀ middle,
      ScopedRegionPair primitives ids mapping restL restR entryL entryR
        (localsL.snoc valueL) (localsR.snoc valueR) middle) :
    ScopedRegionPair primitives ids mapping (bindApplication fn inputs restL) (bindApplication fn inputs restR)
      entryL entryR localsL localsR store := by
  have openL := open_lambda left capL argsL
  have openR := open_lambda right capR argsR
  cases callee with
  | returned values ranL ranR =>
    exact continue_pair (nodeL := applicationVertex fn inputs) (nodeR := applicationVertex fn inputs)
      (application_eval selectL (.call (openL.symm ▸ ranL))) (application_eval selectR (.call (openR.symm ▸ ranR)))
      (resume values _)
  | blocked stopped => exact .blocked (.atCall inputs restL restR selectL selectR stopped)
  | productive run =>
    refine .productive (productive_map run ?_ ?_)
    · intro target pending reached
      exact ⟨.bind restL entryL localsL pending,
        .inside (node := applicationVertex fn inputs) (application_reaches selectL (.call (openL.symm ▸ reached)))⟩
    · intro target pending reached
      exact ⟨.bind restR entryR localsR pending,
        .inside (node := applicationVertex fn inputs) (application_reaches selectR (.call (openR.symm ▸ reached)))⟩

private theorem primitive_pair {past : List (Ports (Ty V S))} {ins head : Ports (Ty V S)}
    {restL : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigsL outs}
    {restR : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigsR outs}
    {entryL entryR : Tuple m.Val args} {localsL localsR : Locals m.Val past}
    (respects : ActionsRespect primitives ids) (opcode : Op ins head) (inputs : Wires args past ins)
    (related : TupleRelated m ids (inputs.read entryL localsL) (inputs.read entryR localsR)) (store : σ)
    (resume : ∀ {valueL valueR : Tuple m.Val head}, TupleRelated m ids valueL valueR → ∀ middle,
      ScopedRegionPair primitives ids mapping restL restR entryL entryR
        (localsL.snoc valueL) (localsR.snoc valueR) middle) :
    ScopedRegionPair primitives ids mapping (bindPrimitive opcode inputs restL) (bindPrimitive opcode inputs restR)
      entryL entryR localsL localsR store := by
  have agreement := respects opcode related store
  generalize ranL : (primitives.step opcode (inputs.read entryL localsL)).run store = resultL at agreement
  generalize ranR : (primitives.step opcode (inputs.read entryR localsR)).run store = resultR at agreement
  cases agreement with
  | undefined => exact .blocked (.atPrimitive opcode inputs related ranL ranR)
  | returned values middle =>
    exact continue_pair (nodeL := primitiveVertex opcode inputs) (nodeR := primitiveVertex opcode inputs)
      (.primitive (primitiveSite opcode _) (ranL.symm ▸ _root_.Part.mem_some _))
      (.primitive (primitiveSite opcode _) (ranR.symm ▸ _root_.Part.mem_some _))
      (resume values middle)

theorem ranked_regions {rank : Nat} {context params : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    {capturesL capturesR : Tuple m.Val context}
    {left : NestedTheta.Term (Instruction Op) (context ++ params) past sigsL outs}
    {right : NestedTheta.Term (Instruction Op) (context ++ params) past sigsR outs}
    (plan : RankedPlan m ids rank mapping capturesL capturesR left right) (respects : ActionsRespect primitives ids)
    (captures : TupleRelated m ids capturesL capturesR)
    {argsL argsR : Tuple m.Val params} (arguments : TupleRelated m ids argsL argsR)
    {localsL localsR : Locals m.Val past} (locals : AlignedLocals m ids localsL localsR) (store : σ) :
    ScopedRegionPair primitives ids mapping left right
      (prependContext argsL capturesL) (prependContext argsR capturesR) localsL localsR store := by
  induction plan generalizing store with
  | body code =>
    cases localsL
    cases localsR
    exact regions code respects (prepend_related captures arguments) store
  | suffix schedule =>
    obtain ⟨_, _, paired⟩ := Local.scoped_evaluate schedule respects (prepend_related captures arguments) locals store
    cases paired with
    | returned values ranL ranR => exact .returned values ranL ranR
    | blocked address sites ranL ranR => exact .blocked (.suffix address sites ranL ranR)
  | @call _ _ _ _ _ _ _ _ _ _ _ _ _ capL capR _ _ _ _ _ _
      port selectedL selectedR captured wires _ _ _ calleeIH suffixIH =>
    have operands := Local.aligned_read (prepend_related captures arguments) locals wires
    have readL := (get_capture port capL argsL).trans selectedL
    have readR := (get_capture port capR argsR).trans selectedR
    exact bind_pair (.cons (.arg (capturePort port)) wires)
      (congrArg (fun callee => Tuple.cons callee (wires.read (prependContext argsL capL) localsL)) readL)
      (congrArg (fun callee => Tuple.cons callee (wires.read (prependContext argsR capR) localsR)) readR)
      (calleeIH captured operands .empty store)
      (fun values middle => suffixIH captures arguments (locals.snoc values) middle)
  | primitive opcode wires _ suffixIH =>
    exact primitive_pair respects opcode wires (Local.aligned_read (prepend_related captures arguments) locals wires)
      store (fun values middle => suffixIH captures arguments (locals.snoc values) middle)

  | @gamma _ _ _ _ _ _ _ _ _ _ _ _ capL capR _ _ _ _ restL restR selector ports wires _ _ armIH suffixIH =>
    have entries := prepend_related captures arguments
    obtain ⟨tag, _, _, selectL, selectR, _⟩ := selected_tuple (Local.aligned_read entries locals (.cons selector .nil))
    have captured := project_related captures ports
    have operands := Local.aligned_read entries locals wires
    exact gamma_scoped (restL := restL) (restR := restR) (armInputs selector ports wires)
      (read_arm_input capL argsL localsL selector ports wires (congrArg (fun v => v.get .head) selectL))
      (read_arm_input capR argsR localsR selector ports wires (congrArg (fun v => v.get .head) selectR))
      (armIH tag captured operands .empty store)
      (fun values middle => suffixIH captures arguments (locals.snoc values) middle)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

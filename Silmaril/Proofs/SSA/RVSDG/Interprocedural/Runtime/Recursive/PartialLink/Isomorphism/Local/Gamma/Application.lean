module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Feedback
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Regions
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Environments
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Captures
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Choice
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
    (arm : Option Nat) (inputs : Wires args past (fn.port :: fn.args))
    (selectL : inputs.read entryL localsL = .cons (.closure capL left.toGraph) argsL)
    (selectR : inputs.read entryR localsR = .cons (.closure capR right.toGraph) argsR)
    (callee : RegionPair primitives ids (mapping.child past.length (arm.getD 0)) left right
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
  | blocked stopped =>
    cases arm with
    | none => exact .blocked (.atCall inputs restL restR selectL selectR stopped)
    | some tag => exact .blocked (.atChosenCall tag inputs restL restR selectL selectR stopped)
  | productive run =>
    refine .productive (productive_map run ?_ ?_)
    · intro target pending reached
      exact ⟨.bind restL entryL localsL pending,
        .inside (node := applicationVertex fn inputs) (application_reaches selectL (.call (openL.symm ▸ reached)))⟩
    · intro target pending reached
      exact ⟨.bind restR entryR localsR pending,
        .inside (node := applicationVertex fn inputs) (application_reaches selectR (.call (openR.symm ▸ reached)))⟩

private theorem choose_after_pair {context params outs : Ports (Ty V S)} {fn : Function V S} {extra : Nat}
    {past final steps tailL tailR : List (Ports (Ty V S))}
    {restL : NestedTheta.Term (Instruction Op) (context ++ params) (final ++ [fn.results]) tailL outs}
    {restR : NestedTheta.Term (Instruction Op) (context ++ params) (final ++ [fn.results]) tailR outs}
    {capL capR : Tuple m.Val context} {argsL argsR : Tuple m.Val params}
    {localsL localsR : Locals m.Val past} {store : σ}
    (respects : ActionsRespect primitives ids) (selector : Origin (context ++ params) past (.control (extra + 2)))
    (ports : Fin (extra + 2) → Port context fn.port)
    (route : ChoicePrefix Op (context ++ params) fn (past ++ [[fn.port]]) final steps)
    (wires : Wires (context ++ params) final fn.args) (family : Fin (extra + 2) → CallTarget m fn)
    (originL : ∀ tag, capL.get (ports tag) = (family tag).valueL)
    (originR : ∀ tag, capR.get (ports tag) = (family tag).valueR)
    (captures : TupleRelated m ids capL capR) (arguments : TupleRelated m ids argsL argsR)
    (locals : AlignedLocals m ids localsL localsR)
    (observe : ∀ tag {operandsL operandsR : Tuple m.Val fn.args}, TupleRelated m ids operandsL operandsR → ∀ middle,
      RegionPair primitives ids (mapping.child final.length tag.val) (family tag).left (family tag).right
        (prependContext operandsL (family tag).capturesL) (prependContext operandsR (family tag).capturesR) middle)
    (resume : ∀ {scopeL scopeR : Locals m.Val (final ++ [fn.results])}, AlignedLocals m ids scopeL scopeR → ∀ middle,
      ScopedRegionPair primitives ids mapping restL restR (prependContext argsL capL)
        (prependContext argsR capR) scopeL scopeR middle) :
    ScopedRegionPair primitives ids mapping (chooseApplicationAfter fn selector ports route wires restL)
      (chooseApplicationAfter fn selector ports route wires restR)
      (prependContext argsL capL) (prependContext argsR capR) localsL localsR store := by
  let source := joinedOrigin (past := past) (args := context ++ params) fn
  let inputs := Tuple.cons (route.callable source) wires
  refine choose_pair (restL := route.wrap source (bindApplication fn inputs restL))
    (restR := route.wrap source (bindApplication fn inputs restR)) selector ports captures arguments locals ?_
  intro tag
  let entryL := prependContext argsL capL
  let entryR := prependContext argsR capR
  let valueL := capL.get (ports tag)
  let valueR := capR.get (ports tag)
  have paired := captures.get (ports tag)
  have entries := prepend_related captures arguments
  refine prefix_pair respects route source entries (locals.snoc (.cons paired .nil)) paired
    (joined_origin_read entryL localsL valueL) (joined_origin_read entryR localsR valueR) ?_
  intro scopeL scopeR middle aligned liveL liveR
  have operands := Local.aligned_read entries aligned wires
  have selectedL : Wires.read inputs entryL scopeL = .cons (family tag).valueL (wires.read entryL scopeL) :=
    congrArg (fun callee => Tuple.cons callee (wires.read entryL scopeL)) (liveL.trans (originL tag))
  have selectedR : Wires.read inputs entryR scopeR = .cons (family tag).valueR (wires.read entryR scopeR) :=
    congrArg (fun callee => Tuple.cons callee (wires.read entryR scopeR)) (liveR.trans (originR tag))
  exact bind_pair (some tag.val) inputs selectedL selectedR (observe tag operands middle)
    (fun values finalStore => resume (aligned.snoc values) finalStore)

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
    exact bind_pair none (.cons (.arg (capturePort port)) wires)
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

  | @theta _ _ _ _ _ _ _ _ _ _ _ _ capL capR bodyL bodyR restL restR ports initial _ fixedL fixedR _ bodyIH suffixIH =>
    have entries := prepend_related captures arguments
    have captured := project_related captures ports
    refine loop_scoped (bodyL := bodyL) (bodyR := bodyR) (restL := restL) (restR := restR)
      (captureInputs ports initial) (Local.aligned_read entries locals (captureInputs ports initial)) ?_ ?_
    · intro current completed
      obtain ⟨nextL, carryL⟩ := feedback_captures fixedL (projectCaptures capL ports)
        ⟨_, read_projected capL argsL localsL ports initial⟩ (left_completed completed)
      obtain ⟨nextR, carryR⟩ := feedback_captures fixedR (projectCaptures capR ports)
        ⟨_, read_projected capR argsR localsR ports initial⟩ (right_completed completed)
      dsimp only at carryL carryR
      have related := current.related
      rw [carryL, carryR] at related ⊢
      exact bodyIH captured (related_arguments related) .empty current.store
    · intro valueL valueR values middle
      exact suffixIH captures arguments (locals.snoc values) middle

  | @choose _ _ _ _ _ _ _ _ _ _ _ _ restL restR selector ports wires family _ originL originR captured
      _ _ _ calleeIH suffixIH =>
    exact choose_after_pair (restL := restL) (restR := restR) respects selector ports .done wires family
      originL originR captures arguments locals
      (fun tag {_ _} operands middle => calleeIH tag (captured tag) operands .empty middle)
      (fun aligned middle => suffixIH captures arguments aligned middle)
  | @chooseAfter _ _ _ _ _ _ _ _ _ _ _ _ _ _ restL restR selector ports route wires family _ originL originR
      captured _ _ _ calleeIH suffixIH =>
    exact choose_after_pair (restL := restL) (restR := restR) respects selector ports route wires family
      originL originR captures arguments locals
      (fun tag {_ _} operands middle => calleeIH tag (captured tag) operands .empty middle)
      (fun aligned middle => suffixIH captures arguments aligned middle)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

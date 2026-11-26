module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Defs

/-! Selected γ composition for ordered partial execution. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma

open Continuation.Partial
open Continuation.Descent (Pending)
open Relation (ReflTransGen)
open SingleTheta (Carries)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {args outs entry returned carried params : Ports (Ty V S)} {extra : Nat}
variable {sigs sigsL sigsR : List (Ports (Ty V S))}

abbrev vertex {past : List (Ports (Ty V S))} (inputs : Wires args past (.control (extra + 2) :: entry))
    (sigs : Fin (extra + 2) → List (Ports (Ty V S))) :
    NestedTheta.Node (Instruction Op) args past returned :=
  ⟨_, .base (.gamma extra), inputs, sigs⟩

/-- Enter the selected γ arm with fresh locals, then bind its result in the parent suffix. -/
abbrev bindGamma {past : List (Ports (Ty V S))}
    (inputs : Wires args past (.control (extra + 2) :: entry))
    {sigs : Fin (extra + 2) → List (Ports (Ty V S))}
    (arms : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigs i) returned)
    (suffix : NestedTheta.Term (Instruction Op) args (past ++ [returned]) sigsL outs) :
    NestedTheta.Term (Instruction Op) args past (returned :: sigsL) outs :=
  .bind (vertex inputs sigs) arms suffix

/-- A single γ followed by its typed result wiring. The suffix may read
the original region arguments as well as the selected arm's outputs. -/
abbrev code (inputs : Wires args [] (.control (extra + 2) :: entry))
    {sigs : Fin (extra + 2) → List (Ports (Ty V S))}
    (arms : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigs i) returned)
    (outputs : Wires args [returned] outs) : NestedTheta.Term (Instruction Op) args [] [returned] outs :=
  bindGamma inputs arms (.ret outputs)

abbrev applicationVertex {past : List (Ports (Ty V S))} (fn : Function V S)
    (inputs : Wires args past (fn.port :: fn.args)) : NestedTheta.Node (Instruction Op) args past fn.results :=
  ⟨_, .base (.simple (.apply fn)), inputs, fun _ => []⟩

/-- Apply the scoped operands and bind all results in the actual typed suffix. -/
abbrev bindApplication {past : List (Ports (Ty V S))} (fn : Function V S)
    (inputs : Wires args past (fn.port :: fn.args))
    (suffix : NestedTheta.Term (Instruction Op) args (past ++ [fn.results]) sigs outs) :
    NestedTheta.Term (Instruction Op) args past (fn.results :: sigs) outs :=
  .bind (applicationVertex fn inputs) (fun i => i.elim0) suffix

/-- A straight-line primitive binding with a scoped suffix. -/
abbrev primitiveVertex {past : List (Ports (Ty V S))} {ins head : Ports (Ty V S)}
    (opcode : Op ins head) (inputs : Wires args past ins) :
    NestedTheta.Node (Instruction Op) args past head :=
  ⟨_, .base (.simple (.primitive opcode)), inputs, fun _ => []⟩

abbrev bindPrimitive {past : List (Ports (Ty V S))} {ins head : Ports (Ty V S)}
    (opcode : Op ins head) (inputs : Wires args past ins)
    (suffix : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigs outs) :
    NestedTheta.Term (Instruction Op) args past (head :: sigs) outs :=
  .bind (primitiveVertex opcode inputs) (fun i => i.elim0) suffix

abbrev primitiveSite {ins head : Ports (Ty V S)} (opcode : Op ins head) (input : Tuple m.Val ins) : Site m :=
  ⟨ins, head, opcode, fun _ => [], fun i => i.elim0, input⟩

/-- A single application followed by its typed result wiring. The
ordinary binding saves the caller's entry and suffix across dispatch. -/
abbrev applicationCode (fn : Function V S) (inputs : Wires args [] (fn.port :: fn.args))
    (outputs : Wires args [fn.results] outs) :
    NestedTheta.Term (Instruction Op) args [] [fn.results] outs :=
  bindApplication fn inputs (.ret outputs)

/-- An application followed by an acyclic ordered continuation. The
result is local binding zero when the actual machine resumes the suffix. -/
abbrev applicationThen (fn : Function V S) (inputs : Wires args [] (fn.port :: fn.args))
    (suffix : Term Op args [fn.results] sigsL outs) :
    NestedTheta.Term (Instruction Op) args [] (fn.results :: sigsL) outs :=
  bindApplication fn inputs (embed suffix)

/-- The application and its closure dispatch share this ordinary
binding frame. The frame saves the entire caller entry. -/
abbrev applicationFrame {head final : Ports (Ty V S)} (outputs : Wires args [head] outs)
    (entry : Tuple m.Val args) (parent : Continuation.Stack m outs final) : Continuation.Stack m head final :=
  .resume (past := []) (.ret outputs) entry PUnit.unit parent

def resumedApplication {head final : Ports (Ty V S)} (outputs : Wires args [head] outs)
    (entry : Tuple m.Val args) (parent : Continuation.Stack m outs final)
    (value : Tuple m.Val head) (store : σ) : Config m σ final :=
  ⟨.eval (.region (.ret outputs) entry (Locals.snoc (past := []) PUnit.unit value)) parent, store⟩

/-- The first actual return of the selected call to its saved binding. -/
abbrev CallReturnsTo {fn : Function V S} {final : Ports (Ty V S)} (primitives : Primitives m σ)
    (callee : m.Val fn.port) (arguments : Tuple m.Val fn.args) (frame : Continuation.Stack m fn.results final)
    (store : σ) (value : Tuple m.Val fn.results) (returnedStore : σ) : Prop :=
  ReflTransGen (InsideStep primitives frame) ⟨.eval (.call callee arguments) frame, store⟩
    ⟨.returned value frame, returnedStore⟩

abbrev LoopBody (Op : Dialect.{u, v} (ValueSort V S) S) (carried : Ports (Ty V S))
    (sigs : List (Ports (Ty V S))) :=
  NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)

abbrev thetaVertex {past : List (Ports (Ty V S))} (initial : Wires args past carried)
    (bodySigs : List (Ports (Ty V S))) : NestedTheta.Node (Instruction Op) args past carried :=
  ⟨carried, .theta carried, initial, fun _ => bodySigs⟩

/-- Run fresh θ activations through exit, then bind the complete carry in the saved suffix. -/
abbrev bindTheta {past : List (Ports (Ty V S))} (initial : Wires args past carried) (body : LoopBody Op carried sigs)
    (suffix : NestedTheta.Term (Instruction Op) args (past ++ [carried]) sigsL outs) :
    NestedTheta.Term (Instruction Op) args past (carried :: sigsL) outs :=
  .bind (thetaVertex initial sigs) (fun _ => body) suffix

/-- An outer θ with a wiring suffix. Its activation is scoped in fresh
locals, and the suffix also has access to the original arguments. -/
abbrev loopCode (initial : Wires args [] carried) (body : LoopBody Op carried sigs)
    (outputs : Wires args [carried] outs) :
    NestedTheta.Term (Instruction Op) args [] [carried] outs :=
  bindTheta initial body (.ret outputs)

/-- A positive outer iteration requires a whole successful activation on
each side, including any inner θ, followed by the actual feedback edge. -/
def IterationPair (primitives : Primitives m σ) (left : LoopBody Op carried sigsL) (right : LoopBody Op carried sigsR)
    (input next : Carries m ids σ carried) : Prop :=
  Feedback.Iteration primitives left (input.left, input.store) (next.left, next.store) ∧
  Feedback.Iteration primitives right (input.right, input.store) (next.right, next.store)

/-- Structural child maps choose a γ arm or θ body. Single-binding
wrappers start at zero. A ranked call records its fixed caller vertex
and uses the separate map of the closure selected there. -/
inductive Location where
  | acyclic (inner : Local.Location)
  | theta (inner : Local.Location)
  | gamma (arm : Nat) (inner : Location)
  | loop (inner : Location)
  | application (inner : Location)
  | suffix (inner : Local.Location)
  | callSite (vertex : Nat) (inner : Location)
  | chosenCall (vertex arm : Nat) (inner : Location)
  | atArm (vertex arm : Nat) (inner : Location)
  | atLoop (vertex : Nat) (inner : Location)
  deriving DecidableEq, Repr

def Location.rename (mapping : Renaming) : Location → Location
  | .acyclic inner => .acyclic (mapping.location inner)
  | .theta inner => .theta ((mapping.child 0 0).location inner)
  | .gamma arm inner => .gamma arm (inner.rename (mapping.child 0 arm))
  | .loop inner => .loop (inner.rename (mapping.child 0 0))
  | .application inner => .application (inner.rename mapping)
  | .suffix inner => .suffix (Renaming.identity.location inner)
  | .callSite vertex inner => .callSite vertex (inner.rename (mapping.child vertex 0))
  | .chosenCall vertex arm inner => .chosenCall vertex arm (inner.rename (mapping.child vertex arm))
  | .atArm vertex arm inner => .atArm vertex arm (inner.rename (mapping.child vertex arm))
  | .atLoop vertex inner => .atLoop vertex (inner.rename (mapping.child vertex 0))

/-- Finite γ/θ trees over ordered acyclic graphs. Each structural binding
uses common typed input and output wiring. Only the selected γ arm is
entered, and θ restarts its own body with fresh locals. -/
inductive CodePair (Op : Dialect.{u, v} (ValueSort V S) S) :
    {args outs : Ports (Ty V S)} → {sigsL sigsR : List (Ports (Ty V S))} →
    Renaming → NestedTheta.Term (Instruction Op) args [] sigsL outs →
    NestedTheta.Term (Instruction Op) args [] sigsR outs → Prop where
  | acyclic {args outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : Graph Op args [] sigsL outs} {right : Graph Op args [] sigsR outs}
      (ordered : OrderedGraph map left right) :
    CodePair Op map (embed left.toTerm) (embed right.toTerm)
  | theta {args carried outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : SingleTheta.Body Op carried sigsL} {right : SingleTheta.Body Op carried sigsR}
      (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
      (position : map.vertices 0 = 0) (ordered : OrderedGraph (map.child 0 0) left right) :
    CodePair Op map (SingleTheta.code initial left outputs) (SingleTheta.code initial right outputs)
  | gamma {args entry returned outs : Ports (Ty V S)} {extra : Nat} {map : Renaming}
      {sigsL sigsR : Fin (extra + 2) → List (Ports (Ty V S))}
      {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsL i) returned}
      {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsR i) returned}
      (inputs : Wires args [] (.control (extra + 2) :: entry)) (outputs : Wires args [returned] outs)
      (position : map.vertices 0 = 0) (arms : ∀ i, CodePair Op (map.child 0 i.val) (armsL i) (armsR i)) :
    CodePair Op map (code inputs armsL outputs) (code inputs armsR outputs)

  | loop {args carried outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : LoopBody Op carried sigsL} {right : LoopBody Op carried sigsR}
      (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
      (position : map.vertices 0 = 0) (body : CodePair Op (map.child 0 0) left right) :
    CodePair Op map (loopCode initial left outputs) (loopCode initial right outputs)

/-- The existing typed primitive diagnostic and exact pending continuation. -/
structure Block (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) (outs : Ports (Ty V S)) where
  site : Site m
  pending : Pending m site.outs outs
  store : σ

def Block.outcome (stop : Block m σ outs) : Continuation.Partial.Outcome m σ outs :=
  .blocked stop.site stop.pending stop.store

/-- Paired addressed blocks with the original entry, live locals and exact pending frames.
A structural node keeps its selected child and saved suffix. An ordered binding either blocks
inside its work or has returned before the witnessed block. -/
inductive ScopedBlockPair (primitives : Primitives m σ) (ids : GlobalRel) :
    {args outs : Ports (Ty V S)} → {pastL pastR sigsL sigsR : List (Ports (Ty V S))} →
    (map : Renaming) →
    NestedTheta.Term (Instruction Op) args pastL sigsL outs →
    NestedTheta.Term (Instruction Op) args pastR sigsR outs →
    Tuple m.Val args → Tuple m.Val args → Locals m.Val pastL → Locals m.Val pastR → σ →
    Location → Location → Block m σ outs → Block m σ outs → Prop where
  | acyclic {args outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : Term Op args [] sigsL outs} {right : Term Op args [] sigsR outs}
      {inputL inputR : Tuple m.Val args} {start store : σ}
      {siteL siteR : Site m} {pendingL : Pending m siteL.outs outs} {pendingR : Pending m siteR.outs outs}
      (location : Local.Location) (sites : SitesRelated m ids siteL siteR)
      (ranL : Local.BlockAt primitives left inputL PUnit.unit start location (.blocked siteL pendingL store))
      (ranR : Local.BlockAt primitives right inputR PUnit.unit start (map.location location) (.blocked siteR pendingR store)) :
    ScopedBlockPair primitives ids map (embed left) (embed right) inputL inputR PUnit.unit PUnit.unit start
      (.acyclic location) (.acyclic (map.location location)) ⟨siteL, pendingL, store⟩ ⟨siteR, pendingR, store⟩
  | theta {args carried outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : SingleTheta.Body Op carried sigsL} {right : SingleTheta.Body Op carried sigsR}
      {entryL entryR : Tuple m.Val args} {start store : σ}
      {first current : SingleTheta.Carries m ids σ carried}
      {siteL siteR : Site m} {pendingL : Pending m siteL.outs (Theta.BodyResults carried)}
      {pendingR : Pending m siteR.outs (Theta.BodyResults carried)}
      (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
      (startsL : first.left = initial.read entryL PUnit.unit) (startsR : first.right = initial.read entryR PUnit.unit)
      (startsStore : first.store = start)
      (completed : ReflTransGen (SingleTheta.FeedbackPair primitives left right) first current)
      (location : Local.Location) (sites : SitesRelated m ids siteL siteR)
      (ranL : Local.BlockAt primitives left.toTerm current.left PUnit.unit current.store
        location (.blocked siteL pendingL store))
      (ranR : Local.BlockAt primitives right.toTerm current.right PUnit.unit current.store
        ((map.child 0 0).location location) (.blocked siteR pendingR store)) :
    ScopedBlockPair primitives ids map (SingleTheta.code initial left outputs) (SingleTheta.code initial right outputs)
      entryL entryR PUnit.unit PUnit.unit start (.theta location) (.theta ((map.child 0 0).location location))
      ⟨siteL, .bind (past := []) (.ret outputs) entryL PUnit.unit (.loop (embed left.toTerm) pendingL), store⟩
      ⟨siteR, .bind (past := []) (.ret outputs) entryR PUnit.unit (.loop (embed right.toTerm) pendingR), store⟩
  | gamma {args entry returned outs : Ports (Ty V S)} {extra : Nat} {map : Renaming}
      {sigsL sigsR : Fin (extra + 2) → List (Ports (Ty V S))}
      {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsL i) returned}
      {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsR i) returned}
      {entryL entryR : Tuple m.Val args} {inputL inputR : Tuple m.Val entry} {store : σ}
      {tag : Fin (extra + 2)} {locL locR : Location} {stopL stopR : Block m σ returned}
      (inputs : Wires args [] (.control (extra + 2) :: entry)) (outputs : Wires args [returned] outs)
      (selectL : inputs.read entryL PUnit.unit = .cons (.control tag) inputL)
      (selectR : inputs.read entryR PUnit.unit = .cons (.control tag) inputR)
      (selected : ScopedBlockPair primitives ids (map.child 0 tag.val) (armsL tag) (armsR tag)
        inputL inputR PUnit.unit PUnit.unit store locL locR stopL stopR) :
    ScopedBlockPair primitives ids map (code inputs armsL outputs) (code inputs armsR outputs) entryL entryR PUnit.unit PUnit.unit store
      (.gamma tag.val locL) (.gamma tag.val locR)
      ⟨stopL.site, .bind (past := []) (.ret outputs) entryL PUnit.unit stopL.pending, stopL.store⟩
      ⟨stopR.site, .bind (past := []) (.ret outputs) entryR PUnit.unit stopR.pending, stopR.store⟩

  | loop {args carried outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : LoopBody Op carried sigsL} {right : LoopBody Op carried sigsR}
      {entryL entryR : Tuple m.Val args} {store : σ} {first current : Carries m ids σ carried}
      {locL locR : Location} {stopL stopR : Block m σ (Theta.BodyResults carried)}
      (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
      (startsL : first.left = initial.read entryL PUnit.unit) (startsR : first.right = initial.read entryR PUnit.unit)
      (startsStore : first.store = store)
      (completed : ReflTransGen (IterationPair primitives left right) first current)
      (stopped : ScopedBlockPair primitives ids (map.child 0 0) left right current.left current.right PUnit.unit PUnit.unit
        current.store locL locR stopL stopR) :
    ScopedBlockPair primitives ids map (loopCode initial left outputs) (loopCode initial right outputs)
      entryL entryR PUnit.unit PUnit.unit store (.loop locL) (.loop locR)
      ⟨stopL.site, .bind (past := []) (.ret outputs) entryL PUnit.unit (.loop left stopL.pending), stopL.store⟩
      ⟨stopR.site, .bind (past := []) (.ret outputs) entryR PUnit.unit (.loop right stopR.pending), stopR.store⟩

  | application {args outs captured : Ports (Ty V S)} {fn : Function V S} {map : Renaming}
      {sigsL sigsR : List (Ports (Ty V S))}
      {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
      {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
      {captL captR : Tuple m.Val captured} {entryL entryR : Tuple m.Val args}
      {argsL argsR : Tuple m.Val fn.args} {store : σ}
      {locL locR : Location} {stopL stopR : Block m σ fn.results}
      (inputs : Wires args [] (fn.port :: fn.args)) (outputs : Wires args [fn.results] outs)
      (selectL : inputs.read entryL PUnit.unit = .cons (.closure captL left.toGraph) argsL)
      (selectR : inputs.read entryR PUnit.unit = .cons (.closure captR right.toGraph) argsR)
      (stopped : ScopedBlockPair primitives ids map left right (prependContext argsL captL) (prependContext argsR captR) PUnit.unit PUnit.unit
        store locL locR stopL stopR) :
    ScopedBlockPair primitives ids map (applicationCode fn inputs outputs) (applicationCode fn inputs outputs)
      entryL entryR PUnit.unit PUnit.unit store (.application locL) (.application locR)
      ⟨stopL.site, .bind (past := []) (.ret outputs) entryL PUnit.unit stopL.pending, stopL.store⟩
      ⟨stopR.site, .bind (past := []) (.ret outputs) entryR PUnit.unit stopR.pending, stopR.store⟩

  | applicationThen {args outs captured : Ports (Ty V S)} {fn : Function V S} {map : Renaming}
      {sigsL sigsR tailL tailR : List (Ports (Ty V S))}
      {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
      {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
      {captL captR : Tuple m.Val captured} {entryL entryR : Tuple m.Val args}
      {argsL argsR : Tuple m.Val fn.args} {store : σ}
      {locL locR : Location} {stopL stopR : Block m σ fn.results}
      (inputs : Wires args [] (fn.port :: fn.args))
      (suffixL : Term Op args [fn.results] tailL outs) (suffixR : Term Op args [fn.results] tailR outs)
      (selectL : inputs.read entryL PUnit.unit = .cons (.closure captL left.toGraph) argsL)
      (selectR : inputs.read entryR PUnit.unit = .cons (.closure captR right.toGraph) argsR)
      (stopped : ScopedBlockPair primitives ids map left right (prependContext argsL captL) (prependContext argsR captR) PUnit.unit PUnit.unit
        store locL locR stopL stopR) :
    ScopedBlockPair primitives ids map (applicationThen fn inputs suffixL) (applicationThen fn inputs suffixR)
      entryL entryR PUnit.unit PUnit.unit store (.application locL) (.application locR)
      ⟨stopL.site, .bind (past := []) (embed suffixL) entryL PUnit.unit stopL.pending, stopL.store⟩
      ⟨stopR.site, .bind (past := []) (embed suffixR) entryR PUnit.unit stopR.pending, stopR.store⟩
  | afterApplication {args outs : Ports (Ty V S)} {fn : Function V S} {map : Renaming}
      {tailL tailR : List (Ports (Ty V S))}
      {entryL entryR : Tuple m.Val args} {calleeL calleeR : m.Val fn.port}
      {argsL argsR : Tuple m.Val fn.args} {valueL valueR : Tuple m.Val fn.results} {store middle stopped : σ}
      {siteL siteR : Site m} {pendingL : Pending m siteL.outs outs} {pendingR : Pending m siteR.outs outs}
      (inputs : Wires args [] (fn.port :: fn.args))
      (suffixL : Term Op args [fn.results] tailL outs) (suffixR : Term Op args [fn.results] tailR outs)
      (selectL : inputs.read entryL PUnit.unit = .cons calleeL argsL)
      (selectR : inputs.read entryR PUnit.unit = .cons calleeR argsR)
      (ranL : Eval primitives (.call calleeL argsL) store (.returned valueL middle))
      (ranR : Eval primitives (.call calleeR argsR) store (.returned valueR middle))
      (location : Local.Location) (sites : SitesRelated m ids siteL siteR)
      (blockedL : Local.BlockAt primitives suffixL entryL (Locals.snoc (past := []) PUnit.unit valueL)
        middle location (.blocked siteL pendingL stopped))
      (blockedR : Local.BlockAt primitives suffixR entryR (Locals.snoc (past := []) PUnit.unit valueR)
        middle (Renaming.identity.location location) (.blocked siteR pendingR stopped)) :
    ScopedBlockPair primitives ids map (applicationThen fn inputs suffixL) (applicationThen fn inputs suffixR)
      entryL entryR PUnit.unit PUnit.unit store (.suffix location) (.suffix (Renaming.identity.location location))
      ⟨siteL, pendingL, stopped⟩ ⟨siteR, pendingR, stopped⟩

  | suffix {args outs : Ports (Ty V S)} {past : List (Ports (Ty V S))}
      {sigsL sigsR : List (Ports (Ty V S))} {map : Renaming}
      {left : Term Op args past sigsL outs} {right : Term Op args past sigsR outs}
      {entryL entryR : Tuple m.Val args} {localsL localsR : Locals m.Val past} {start store : σ}
      {siteL siteR : Site m} {pendingL : Pending m siteL.outs outs} {pendingR : Pending m siteR.outs outs}
      (location : Local.Location) (sites : SitesRelated m ids siteL siteR)
      (ranL : Local.BlockAt primitives left entryL localsL start location (.blocked siteL pendingL store))
      (ranR : Local.BlockAt primitives right entryR localsR start
        (Renaming.identity.location location) (.blocked siteR pendingR store)) :
    ScopedBlockPair primitives ids map (embed left) (embed right) entryL entryR localsL localsR start
      (.suffix location) (.suffix (Renaming.identity.location location)) ⟨siteL, pendingL, store⟩ ⟨siteR, pendingR, store⟩
  | atCall {args outs captured : Ports (Ty V S)} {fn : Function V S} {map : Renaming}
      {past sigsL sigsR tailL tailR : List (Ports (Ty V S))}
      {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
      {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
      {captL captR : Tuple m.Val captured} {entryL entryR : Tuple m.Val args} {localsL localsR : Locals m.Val past}
      {argsL argsR : Tuple m.Val fn.args} {store : σ}
      {locL locR : Location} {stopL stopR : Block m σ fn.results}
      (inputs : Wires args past (fn.port :: fn.args))
      (suffixL : NestedTheta.Term (Instruction Op) args (past ++ [fn.results]) tailL outs)
      (suffixR : NestedTheta.Term (Instruction Op) args (past ++ [fn.results]) tailR outs)
      (selectL : inputs.read entryL localsL = .cons (.closure captL left.toGraph) argsL)
      (selectR : inputs.read entryR localsR = .cons (.closure captR right.toGraph) argsR)
      (stopped : ScopedBlockPair primitives ids (map.child past.length 0) left right
        (prependContext argsL captL) (prependContext argsR captR) PUnit.unit PUnit.unit store locL locR stopL stopR) :
    ScopedBlockPair primitives ids map (bindApplication fn inputs suffixL) (bindApplication fn inputs suffixR)
      entryL entryR localsL localsR store (.callSite past.length locL) (.callSite past.length locR)
      ⟨stopL.site, .bind suffixL entryL localsL stopL.pending, stopL.store⟩
      ⟨stopR.site, .bind suffixR entryR localsR stopR.pending, stopR.store⟩
  | atChosenCall {args outs captured : Ports (Ty V S)} {fn : Function V S} {map : Renaming}
      {past sigsL sigsR tailL tailR : List (Ports (Ty V S))}
      {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
      {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
      {captL captR : Tuple m.Val captured} {entryL entryR : Tuple m.Val args} {localsL localsR : Locals m.Val past}
      {argsL argsR : Tuple m.Val fn.args} {store : σ}
      {locL locR : Location} {stopL stopR : Block m σ fn.results}
      (arm : Nat) (inputs : Wires args past (fn.port :: fn.args))
      (suffixL : NestedTheta.Term (Instruction Op) args (past ++ [fn.results]) tailL outs)
      (suffixR : NestedTheta.Term (Instruction Op) args (past ++ [fn.results]) tailR outs)
      (selectL : inputs.read entryL localsL = .cons (.closure captL left.toGraph) argsL)
      (selectR : inputs.read entryR localsR = .cons (.closure captR right.toGraph) argsR)
      (stopped : ScopedBlockPair primitives ids (map.child past.length arm) left right
        (prependContext argsL captL) (prependContext argsR captR) PUnit.unit PUnit.unit store locL locR stopL stopR) :
    ScopedBlockPair primitives ids map (bindApplication fn inputs suffixL) (bindApplication fn inputs suffixR)
      entryL entryR localsL localsR store (.chosenCall past.length arm locL) (.chosenCall past.length arm locR)
      ⟨stopL.site, .bind suffixL entryL localsL stopL.pending, stopL.store⟩
      ⟨stopR.site, .bind suffixR entryR localsR stopR.pending, stopR.store⟩
  | atArm {args entry returned outs : Ports (Ty V S)} {extra : Nat} {map : Renaming}
      {past tailL tailR : List (Ports (Ty V S))}
      {sigsL sigsR : Fin (extra + 2) → List (Ports (Ty V S))}
      {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsL i) returned}
      {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (sigsR i) returned}
      {suffixL : NestedTheta.Term (Instruction Op) args (past ++ [returned]) tailL outs}
      {suffixR : NestedTheta.Term (Instruction Op) args (past ++ [returned]) tailR outs}
      {entryL entryR : Tuple m.Val args} {localsL localsR : Locals m.Val past}
      {inputL inputR : Tuple m.Val entry} {store : σ}
      {tag : Fin (extra + 2)} {locL locR : Location} {stopL stopR : Block m σ returned}
      (inputs : Wires args past (.control (extra + 2) :: entry))
      (selectL : inputs.read entryL localsL = .cons (.control tag) inputL)
      (selectR : inputs.read entryR localsR = .cons (.control tag) inputR)
      (selected : ScopedBlockPair primitives ids (map.child past.length tag.val) (armsL tag) (armsR tag)
        inputL inputR PUnit.unit PUnit.unit store locL locR stopL stopR) :
    ScopedBlockPair primitives ids map (bindGamma inputs armsL suffixL) (bindGamma inputs armsR suffixR)
      entryL entryR localsL localsR store (.atArm past.length tag.val locL) (.atArm past.length tag.val locR)
      ⟨stopL.site, .bind suffixL entryL localsL stopL.pending, stopL.store⟩
      ⟨stopR.site, .bind suffixR entryR localsR stopR.pending, stopR.store⟩

  | atLoop {args carried outs : Ports (Ty V S)} {map : Renaming}
      {past sigsL sigsR tailL tailR : List (Ports (Ty V S))}
      {left : LoopBody Op carried sigsL} {right : LoopBody Op carried sigsR}
      {restL : NestedTheta.Term (Instruction Op) args (past ++ [carried]) tailL outs}
      {restR : NestedTheta.Term (Instruction Op) args (past ++ [carried]) tailR outs}
      {entryL entryR : Tuple m.Val args} {localsL localsR : Locals m.Val past}
      {store : σ} {first current : Carries m ids σ carried}
      {locL locR : Location} {stopL stopR : Block m σ (Theta.BodyResults carried)}
      (initial : Wires args past carried)
      (startsL : first.left = initial.read entryL localsL) (startsR : first.right = initial.read entryR localsR)
      (startsStore : first.store = store)
      (completed : ReflTransGen (IterationPair primitives left right) first current)
      (stopped : ScopedBlockPair primitives ids (map.child past.length 0) left right
        current.left current.right PUnit.unit PUnit.unit current.store locL locR stopL stopR) :
    ScopedBlockPair primitives ids map (bindTheta initial left restL) (bindTheta initial right restR)
      entryL entryR localsL localsR store (.atLoop past.length locL) (.atLoop past.length locR)
      ⟨stopL.site, .bind restL entryL localsL (.loop left stopL.pending), stopL.store⟩
      ⟨stopR.site, .bind restR entryR localsR (.loop right stopR.pending), stopR.store⟩
  | atPrimitive {args outs ins head : Ports (Ty V S)} {map : Renaming}
      {past sigsL sigsR : List (Ports (Ty V S))}
      {suffixL : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigsL outs}
      {suffixR : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigsR outs}
      {entryL entryR : Tuple m.Val args} {localsL localsR : Locals m.Val past} {store : σ}
      (opcode : Op ins head) (inputs : Wires args past ins)
      (related : TupleRelated m ids (inputs.read entryL localsL) (inputs.read entryR localsR))
      (undefinedL : (primitives.step opcode (inputs.read entryL localsL)).run store = _root_.Part.none)
      (undefinedR : (primitives.step opcode (inputs.read entryR localsR)).run store = _root_.Part.none) :
    ScopedBlockPair primitives ids map (bindPrimitive opcode inputs suffixL) (bindPrimitive opcode inputs suffixR)
      entryL entryR localsL localsR store (.suffix (.here past.length)) (.suffix (.here past.length))
      ⟨primitiveSite opcode (inputs.read entryL localsL), .bind suffixL entryL localsL .empty, store⟩
      ⟨primitiveSite opcode (inputs.read entryR localsR), .bind suffixR entryR localsR .empty, store⟩
  | later {args outs head : Ports (Ty V S)} {map : Renaming}
      {past tailL tailR : List (Ports (Ty V S))}
      {nodeL nodeR : NestedTheta.Node (Instruction Op) args past head}
      {childrenL : Bodies nodeL.kind nodeL.childSigs} {childrenR : Bodies nodeR.kind nodeR.childSigs}
      {suffixL : NestedTheta.Term (Instruction Op) args (past ++ [head]) tailL outs}
      {suffixR : NestedTheta.Term (Instruction Op) args (past ++ [head]) tailR outs}
      {entryL entryR : Tuple m.Val args} {localsL localsR : Locals m.Val past}
      {valueL valueR : Tuple m.Val head} {store middle : σ} {locL locR : Location} {stopL stopR : Block m σ outs}
      (firstL : Eval primitives (.node nodeL.kind nodeL.childSigs childrenL (nodeL.inputs.read entryL localsL))
        store (.returned valueL middle))
      (firstR : Eval primitives (.node nodeR.kind nodeR.childSigs childrenR (nodeR.inputs.read entryR localsR))
        store (.returned valueR middle))
      (more : ScopedBlockPair primitives ids map suffixL suffixR entryL entryR
        (localsL.snoc valueL) (localsR.snoc valueR) middle locL locR stopL stopR) :
    ScopedBlockPair primitives ids map (.bind nodeL childrenL suffixL) (.bind nodeR childrenR suffixR)
      entryL entryR localsL localsR store locL locR stopL stopR

/-- A paired block from a fresh region entry. -/
abbrev BlockPair (primitives : Primitives m σ) (ids : GlobalRel) (map : Renaming)
    (left : NestedTheta.Term (Instruction Op) args [] sigsL outs)
    (right : NestedTheta.Term (Instruction Op) args [] sigsR outs) (entryL entryR : Tuple m.Val args)
    (store : σ) (locL locR : Location) (stopL stopR : Block m σ outs) : Prop :=
  ScopedBlockPair primitives ids map left right entryL entryR PUnit.unit PUnit.unit store locL locR stopL stopR

namespace BlockPair
export ScopedBlockPair (acyclic theta gamma loop application applicationThen afterApplication)
end BlockPair

variable {primitives : Primitives m σ} {mapping : Renaming}

/-- A common productive feedback stream and finite syntax-directed routes
to its first checkpoints. Both routes retain all pending typed frames. -/
inductive ProductivePair (primitives : Primitives m σ) (ids : GlobalRel)
    {outs : Ports (Ty V S)} (jobL jobR : Job m outs) (store : σ) : Prop where
  | reached {carried : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {left : SingleTheta.Body Op carried sigsL} {right : SingleTheta.Body Op carried sigsR}
      {initial : SingleTheta.Carries m ids σ carried}
      {pendingL pendingR : Pending m carried outs}
      (paired : InfiniteTrace (SingleTheta.FeedbackPair primitives left right) initial)
      (ranL : Feedback.Reaches primitives jobL store ⟨carried, sigsL, embed left.toTerm, (initial.left, initial.store)⟩ pendingL)
      (ranR : Feedback.Reaches primitives jobR store ⟨carried, sigsR, embed right.toTerm, (initial.right, initial.store)⟩ pendingR)

  | feedback {carried : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {left : LoopBody Op carried sigsL} {right : LoopBody Op carried sigsR}
      {initial : Carries m ids σ carried}
      {pendingL pendingR : Pending m carried outs}
      (paired : InfiniteTrace (IterationPair primitives left right) initial)
      (ranL : Feedback.Reaches primitives jobL store ⟨carried, sigsL, left, (initial.left, initial.store)⟩ pendingL)
      (ranR : Feedback.Reaches primitives jobR store ⟨carried, sigsR, right, (initial.right, initial.store)⟩ pendingR)

inductive ScopedRegionPair (primitives : Primitives m σ) (ids : GlobalRel) (mapping : Renaming)
    {pastL pastR : List (Ports (Ty V S))}
    (left : NestedTheta.Term (Instruction Op) args pastL sigsL outs)
    (right : NestedTheta.Term (Instruction Op) args pastR sigsR outs)
    (inputL inputR : Tuple m.Val args) (localsL : Locals m.Val pastL) (localsR : Locals m.Val pastR)
    (store : σ) : Prop where
  | returned {leftValue rightValue : Tuple m.Val outs} {finalStore : σ}
      (values : TupleRelated m ids leftValue rightValue)
      (ranL : Eval primitives (.region left inputL localsL) store (.returned leftValue finalStore))
      (ranR : Eval primitives (.region right inputR localsR) store (.returned rightValue finalStore))
  | blocked {locL locR : Location} {stopL stopR : Block m σ outs}
      (stopped : ScopedBlockPair primitives ids mapping left right inputL inputR localsL localsR store locL locR stopL stopR)
  | productive (run : ProductivePair primitives ids (.region left inputL localsL) (.region right inputR localsR) store)

/-- Paired observations from a fresh region entry. -/
abbrev RegionPair (primitives : Primitives m σ) (ids : GlobalRel) (mapping : Renaming)
    (left : NestedTheta.Term (Instruction Op) args [] sigsL outs)
    (right : NestedTheta.Term (Instruction Op) args [] sigsR outs)
    (inputL inputR : Tuple m.Val args) (store : σ) : Prop :=
  ScopedRegionPair primitives ids mapping left right inputL inputR PUnit.unit PUnit.unit store

namespace RegionPair
export ScopedRegionPair (returned blocked productive)
end RegionPair

/-- An activation that does not select outer feedback. An inner run is
witnessed by the selected arm's productive feedback certificate. -/
inductive Activation (primitives : Primitives m σ) (mapping : Renaming)
    (left : LoopBody Op carried sigsL) (right : LoopBody Op carried sigsR)
    (input : Carries m ids σ carried) : Prop where
  | exited {tag : m.Val (.control 2)} {outL outR : Tuple m.Val carried} {store : σ}
      (exits : (tag.selector.val == 1) = false)
      (values : TupleRelated m ids outL outR)
      (ranL : Eval primitives (.region left input.left PUnit.unit) input.store (.returned (.cons tag outL) store))
      (ranR : Eval primitives (.region right input.right PUnit.unit) input.store (.returned (.cons tag outR) store))
  | blocked {locL locR : Location} {stopL stopR : Block m σ (Theta.BodyResults carried)}
      (stopped : BlockPair primitives ids mapping left right input.left input.right input.store locL locR stopL stopR)
  | inner (live : ProductivePair primitives ids (.region left input.left PUnit.unit)
      (.region right input.right PUnit.unit) input.store)

/-- The observed loop either reaches an exit, block or productive inner
activation after completed outer restarts, or keeps completing outer
activations forever. The prefix and stream use the same carried relation. -/
inductive LoopPair (primitives : Primitives m σ) (mapping : Renaming)
    (left : LoopBody Op carried sigsL) (right : LoopBody Op carried sigsR)
    (input : Carries m ids σ carried) : Prop where
  | activation {current : Carries m ids σ carried}
      (completed : ReflTransGen (IterationPair primitives left right) input current)
      (observed : Activation primitives mapping left right current)
  | outer (live : InfiniteTrace (IterationPair primitives left right) input)

/-- A finite, statically matched chain of captured λs. Leaves may use
the full call-free γ/θ witness. Each application follows the actual first
capture with a strictly smaller rank and has an acyclic ordered suffix
at fixed addresses. Regular arguments can supply operands, while the
selected callable is fixed by the plan. -/
inductive CallPlan (m : Machine.{u, v, w} Op) (ids : GlobalRel) (mapping : Renaming) :
    Nat → {context params outs : Ports (Ty V S)} → {sigsL sigsR : List (Ports (Ty V S))} →
    Tuple m.Val context → Tuple m.Val context →
    NestedTheta.Term (Instruction Op) (context ++ params) [] sigsL outs →
    NestedTheta.Term (Instruction Op) (context ++ params) [] sigsR outs → Prop where
  | body {context params outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {captL captR : Tuple m.Val context}
      {left : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsL outs}
      {right : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsR outs}
      (captures : TupleRelated m ids captL captR) (code : CodePair Op mapping left right) :
    CallPlan m ids mapping 0 captL captR left right
  | application {rank : Nat} {captured context params outs : Ports (Ty V S)} {fn : Function V S}
      {sigsL sigsR tailL tailR : List (Ports (Ty V S))}
      {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
      {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
      {calleeL calleeR : Tuple m.Val captured} {capturesL capturesR : Tuple m.Val context}
      {suffixL : Term Op (fn.port :: (context ++ params)) [fn.results] tailL outs}
      {suffixR : Term Op (fn.port :: (context ++ params)) [fn.results] tailR outs}
      (callee : CallPlan m ids mapping rank calleeL calleeR left right)
      (calleeIso : NestedTheta.Graph.Isomorphic (Instruction Op) left.toGraph right.toGraph)
      (captures : TupleRelated m ids capturesL capturesR)
      (arguments : Wires (fn.port :: (context ++ params)) [] fn.args)
      (suffix : Local.Schedule Op .identity suffixL suffixR) :
    CallPlan m ids mapping (rank + 1)
      (.cons (.closure calleeL left.toGraph) capturesL) (.cons (.closure calleeR right.toGraph) capturesR)
      (applicationThen fn (.cons (.arg .head) arguments) suffixL)
      (applicationThen fn (.cons (.arg .head) arguments) suffixR)

/-- Embed a port of the ordered closure captures into the full λ entry. -/
def capturePort {context : Ports (Ty V S)} {t : Ty V S} :
    Port context t → Port (context ++ params) t
  | .head => .head
  | .tail port => .tail (capturePort port)

/-- Read the selected ordered captures from the parent closure. -/
def projectCaptures {F : Ty V S → Type w} {context childContext : Ports (Ty V S)}
    (captures : Tuple F context) (ports : Tuple (Port context) childContext) : Tuple F childContext :=
  ports.map (fun _ port => captures.get port)

/-- Route known capture ports before the ordinary operand tuple. -/
def captureInputs {context childContext childArgs : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (ports : Tuple (Port context) childContext) (arguments : Wires (context ++ params) past childArgs) :
    Wires (context ++ params) past (childContext ++ childArgs) :=
  prependContext arguments (ports.map (fun _ port => .arg (capturePort port)))

/-- The actual γ boundary orders the selector, chosen capture ports and ordinary operands.
Only the statically routed capture prefix is available for selecting a call target. -/
def armInputs {context childContext childArgs : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (selector : Origin (context ++ params) past (.control (extra + 2)))
    (ports : Tuple (Port context) childContext)
    (arguments : Wires (context ++ params) past childArgs) :
    Wires (context ++ params) past (.control (extra + 2) :: (childContext ++ childArgs)) :=
  .cons selector (captureInputs ports arguments)

/-- A θ body returns the selector followed by the original capture prefix
and its newly computed ordinary carry. -/
def loopOutputs {context : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (selector : Origin (context ++ params) past (.control 2)) (outputs : Wires (context ++ params) past params) :
    Wires (context ++ params) past (Theta.BodyResults (context ++ params)) :=
  .cons selector (captureInputs (NestedTheta.identityPorts context) outputs)

/-- Check the provenance of the capture prefix in a θ body's final result
wiring. A successful spine can compute its other outputs through any
admitted binding. The prefix itself reads the original entry ports. -/
inductive PreservesLoopCaptures (Op : Dialect.{u, v} (ValueSort V S) S) (context params : Ports (Ty V S)) :
    {past bodySigs : List (Ports (Ty V S))} →
    NestedTheta.Term (Instruction Op) (context ++ params) past bodySigs (Theta.BodyResults (context ++ params)) →
    Prop where
  | ret {past : List (Ports (Ty V S))} (selector : Origin (context ++ params) past (.control 2))
      (outputs : Wires (context ++ params) past params) :
    PreservesLoopCaptures Op context params (.ret (loopOutputs selector outputs))
  | bind {past tail : List (Ports (Ty V S))} {head : Ports (Ty V S)}
      {node : NestedTheta.Node (Instruction Op) (context ++ params) past head} {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) (context ++ params) (past ++ [head]) tail (Theta.BodyResults (context ++ params))}
      (suffix : PreservesLoopCaptures Op context params rest) :
    PreservesLoopCaptures Op context params (.bind node children rest)

/-- The chooser arms return one callable port and perform no other work. -/
abbrev chooserArms {context : Ports (Ty V S)} {fn : Function V S}
    (ports : Fin (extra + 2) → Port context fn.port) (tag : Fin (extra + 2)) :
    NestedTheta.Term (Instruction Op) context [] [] [fn.port] :=
  .ret (.cons (.arg (ports tag)) .nil)

def chooserInputs {context : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (selector : Origin (context ++ params) past (.control (extra + 2))) :
    Wires (context ++ params) past (.control (extra + 2) :: context) :=
  .cons selector ((NestedTheta.identityPorts context).map (fun _ port => .arg (capturePort port)))

abbrev joinedOrigin {past : List (Ports (Ty V S))} (fn : Function V S) :
    Origin args (past ++ [[fn.port]]) fn.port :=
  (Tail.Prefix.forwarding args past [fn.port]).get .head

/-- The next application reads its callable from the just-bound γ
output. Its ordinary arguments may read the full caller scope. -/
abbrev joinedInputs {past : List (Ports (Ty V S))} (fn : Function V S)
    (arguments : Wires args (past ++ [[fn.port]]) fn.args) :
    Wires args (past ++ [[fn.port]]) (fn.port :: fn.args) :=
  .cons (joinedOrigin fn) arguments

abbrev chooseApplication {context : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (fn : Function V S) (selector : Origin (context ++ params) past (.control (extra + 2)))
    (ports : Fin (extra + 2) → Port context fn.port)
    (arguments : Wires (context ++ params) (past ++ [[fn.port]]) fn.args)
    (suffix : NestedTheta.Term (Instruction Op) (context ++ params) ((past ++ [[fn.port]]) ++ [fn.results]) sigs outs) :
    NestedTheta.Term (Instruction Op) (context ++ params) past ([fn.port] :: fn.results :: sigs) outs :=
  bindGamma (chooserInputs selector) (chooserArms ports)
    (bindApplication fn (joinedInputs (past := past) fn arguments) suffix)

/-- Extend a wire's scope by one new binding, retaining its producer and port. -/
def extendOrigin {past : List (Ports (Ty V S))} {t : Ty V S}
    (wire : Origin args past t) (head : Ports (Ty V S)) : Origin args (past ++ [head]) t :=
  match wire with
  | .arg port => .arg port
  | .output vertex port =>
    let next : Fin (past ++ [head]).length := ⟨vertex.val, by simp; omega⟩
    have same : (past ++ [head])[next] = past[vertex] := List.getElem_append_left vertex.isLt
    .output next (same.symm ▸ port)

/-- Read the carried callable from the fresh θ result binding. -/
abbrev loopOrigin {past : List (Ports (Ty V S))} (fn : Function V S) (carry : Ports (Ty V S)) :
    Origin args (past ++ [fn.port :: carry]) fn.port :=
  (Tail.Prefix.forwarding args past (fn.port :: carry)).get .head

/-- A finite intervening prefix in the same caller. A primitive adds a
binding while keeping the old callable origin. A forwarding γ copies
that callable to a fresh binding through any of its arms. A θ carries
the callable in the first port, which the body forwards on every return. -/
inductive ChoicePrefix (Op : Dialect.{u, v} (ValueSort V S) S) (args : Ports (Ty V S)) (fn : Function V S) :
    List (Ports (Ty V S)) → List (Ports (Ty V S)) → List (Ports (Ty V S)) → Type (max u v) where
  | done {past : List (Ports (Ty V S))} : ChoicePrefix Op args fn past past []
  | primitive {past final sigs : List (Ports (Ty V S))} {ins head : Ports (Ty V S)}
      (opcode : Op ins head) (inputs : Wires args past ins)
      (rest : ChoicePrefix Op args fn (past ++ [head]) final sigs) : ChoicePrefix Op args fn past final (head :: sigs)
  | forward {past final sigs : List (Ports (Ty V S))} {extra : Nat}
      (selector : Origin args past (.control (extra + 2)))
      (rest : ChoicePrefix Op args fn (past ++ [[fn.port]]) final sigs) :
    ChoicePrefix Op args fn past final ([fn.port] :: sigs)

  | theta {past final sigs bodySigs : List (Ports (Ty V S))} {carry : Ports (Ty V S)}
      (initial : Wires args past carry) (body : LoopBody Op (fn.port :: carry) bodySigs)
      (fixed : PreservesLoopCaptures Op [fn.port] carry body)
      (rest : ChoicePrefix Op args fn (past ++ [fn.port :: carry]) final sigs) :
    ChoicePrefix Op args fn past final ((fn.port :: carry) :: sigs)

/-- The loop uses the ordered call-free witness at its actual child address.
The enclosing prefix uses common binding positions and wiring. -/
def ChoicePrefix.Ordered {fn : Function V S} {past final steps : List (Ports (Ty V S))}
    (route : ChoicePrefix Op args fn past final steps) (map : Renaming) : Prop :=
  match route with
  | .done => True
  | .primitive _ _ rest => rest.Ordered map
  | .forward _ rest => rest.Ordered map
  | @theta _ _ _ _ _ past _ _ _ _ _ body _ rest =>
    map.vertices past.length = past.length ∧ CodePair Op (map.child past.length 0) body body ∧ rest.Ordered map

/-- The typed origin used by the later application. -/
def ChoicePrefix.callable {fn : Function V S} {past final steps : List (Ports (Ty V S))}
    (route : ChoicePrefix Op args fn past final steps) (source : Origin args past fn.port) :
    Origin args final fn.port :=
  match route with
  | .done => source
  | .primitive _ _ rest => rest.callable (extendOrigin source _)
  | .forward _ rest => rest.callable (joinedOrigin fn)
  | .theta _ _ _ rest => rest.callable (loopOrigin fn _)

/-- Insert the actual primitive, forwarding γ, and θ bindings before the suffix. -/
def ChoicePrefix.wrap {fn : Function V S} {past final steps : List (Ports (Ty V S))}
    (route : ChoicePrefix Op args fn past final steps) (source : Origin args past fn.port)
    (suffix : NestedTheta.Term (Instruction Op) args final sigs outs) :
    NestedTheta.Term (Instruction Op) args past (steps ++ sigs) outs :=
  match route with
  | .done => suffix
  | .primitive opcode inputs rest => bindPrimitive opcode inputs (rest.wrap (extendOrigin source _) suffix)
  | .forward selector rest =>
    bindGamma (.cons selector (.cons source .nil)) (chooserArms (fn := fn) (fun _ => .head))
      (rest.wrap (joinedOrigin fn) suffix)
  | .theta initial body _ rest =>
    bindTheta (.cons source initial) body (rest.wrap (loopOrigin fn _) suffix)

abbrev chooseApplicationAfter {context : Ports (Ty V S)} {past final steps : List (Ports (Ty V S))}
    (fn : Function V S) (selector : Origin (context ++ params) past (.control (extra + 2)))
    (ports : Fin (extra + 2) → Port context fn.port)
    (route : ChoicePrefix Op (context ++ params) fn (past ++ [[fn.port]]) final steps)
    (arguments : Wires (context ++ params) final fn.args)
    (suffix : NestedTheta.Term (Instruction Op) (context ++ params) (final ++ [fn.results]) sigs outs) :
    NestedTheta.Term (Instruction Op) (context ++ params) past ([fn.port] :: (steps ++ (fn.results :: sigs))) outs :=
  let source := joinedOrigin (past := past) fn
  bindGamma (chooserInputs selector) (chooserArms ports)
    (route.wrap source (bindApplication fn (.cons (route.callable source) arguments) suffix))

/-- Choose a captured λ once, then carry it as the first θ operand. The
body can read that port directly on every restart. -/
abbrev chooseTheta {context carry : Ports (Ty V S)} {past bodySigs : List (Ports (Ty V S))}
    (fn : Function V S) (selector : Origin (context ++ params) past (.control (extra + 2)))
    (ports : Fin (extra + 2) → Port context fn.port)
    (initial : Wires (context ++ params) (past ++ [[fn.port]]) carry)
    (body : LoopBody Op (fn.port :: carry) bodySigs)
    (suffix : NestedTheta.Term (Instruction Op) (context ++ params) ((past ++ [[fn.port]]) ++ [fn.port :: carry]) sigs outs) :
    NestedTheta.Term (Instruction Op) (context ++ params) past ([fn.port] :: (fn.port :: carry) :: sigs) outs :=
  bindGamma (chooserInputs selector) (chooserArms ports)
    (bindTheta (.cons (joinedOrigin fn) initial) body suffix)

/-- The family captures stay in the leading context. The remaining carry
stores the member index, actual callable, and ordinary loop arguments. -/
abbrev FamilyArgs (fn : Function V S) (extra : Nat) (carry : Ports (Ty V S)) : Ports (Ty V S) :=
  .control (extra + 2) :: fn.port :: carry

abbrev familyValue {context carry : Ports (Ty V S)} {fn : Function V S}
    (ports : Fin (extra + 2) → Port context fn.port) (captures : Tuple m.Val context)
    (tag : Fin (extra + 2)) (input : Tuple m.Val carry) :
    Tuple m.Val (context ++ FamilyArgs fn extra carry) :=
  prependContext (.cons (.control tag) (.cons (captures.get (ports tag)) input)) captures

/-- Both sides hold the same member index and their respective original
capture at that index. Ordinary carried inputs are related independently. -/
def FamilyPair {context carry : Ports (Ty V S)} {fn : Function V S}
    (ports : Fin (extra + 2) → Port context fn.port) (capL capR : Tuple m.Val context)
    (left right : Tuple m.Val (context ++ FamilyArgs fn extra carry)) : Prop :=
  ∃ tag inputL inputR, TupleRelated m ids inputL inputR ∧
    left = familyValue ports capL tag inputL ∧ right = familyValue ports capR tag inputR

/-- Lift an ordinary entry port past the leading capture context. -/
def parameterPort (context : Ports (Ty V S)) {params : Ports (Ty V S)} {t : Ty V S}
    (port : Port params t) : Port (context ++ params) t :=
  match context with
  | [] => port
  | _ :: rest => .tail (parameterPort rest port)

abbrev familyApplicationInputs {context carry : Ports (Ty V S)} (fn : Function V S) {extra : Nat}
    (arguments : Wires (context ++ FamilyArgs fn extra carry) [] fn.args) :
    Wires (context ++ FamilyArgs fn extra carry) [] (fn.port :: fn.args) :=
  .cons (.arg (parameterPort context (.tail .head))) arguments

abbrev familyWires {context params carry : Ports (Ty V S)} {past : List (Ports (Ty V S))} (fn : Function V S)
    (selector : Origin (context ++ params) past (.control (extra + 2)))
    (initial : Wires (context ++ params) (past ++ [[fn.port]]) carry) :
    Wires (context ++ params) (past ++ [[fn.port]]) (context ++ FamilyArgs fn extra carry) :=
  captureInputs (NestedTheta.identityPorts context)
    (.cons (extendOrigin selector [fn.port]) (.cons (joinedOrigin (past := past) fn) initial))

abbrev familyOutputs {context carry : Ports (Ty V S)} (fn : Function V S) {extra : Nat}
    (select : Origin (context ++ FamilyArgs fn extra carry) [fn.results] (.control (extra + 2)))
    (feedback : Origin (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]] (.control 2))
    (ordinary : Wires (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]] carry) :
    Wires (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]]
      (Theta.BodyResults (context ++ FamilyArgs fn extra carry)) :=
  .cons feedback (familyWires (past := [fn.results]) fn select ordinary)

abbrev familyTail {context carry : Ports (Ty V S)} (fn : Function V S)
    (ports : Fin (extra + 2) → Port context fn.port)
    (select : Origin (context ++ FamilyArgs fn extra carry) [fn.results] (.control (extra + 2)))
    (feedback : Origin (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]] (.control 2))
    (ordinary : Wires (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]] carry) :
    NestedTheta.Term (Instruction Op) (context ++ FamilyArgs fn extra carry) [fn.results] [[fn.port]]
      (Theta.BodyResults (context ++ FamilyArgs fn extra carry)) :=
  bindGamma (chooserInputs select) (chooserArms ports) (.ret (familyOutputs fn select feedback ordinary))

/-- Each body activation calls its carried closure. The following γ selects
the next callable from the fixed family captures. -/
abbrev familyBody {context carry : Ports (Ty V S)} (fn : Function V S)
    (ports : Fin (extra + 2) → Port context fn.port)
    (arguments : Wires (context ++ FamilyArgs fn extra carry) [] fn.args)
    (select : Origin (context ++ FamilyArgs fn extra carry) [fn.results] (.control (extra + 2)))
    (feedback : Origin (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]] (.control 2))
    (ordinary : Wires (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]] carry) :
    LoopBody Op (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]] :=
  bindApplication fn (familyApplicationInputs fn arguments) (familyTail fn ports select feedback ordinary)

abbrev switchTheta {context params carry : Ports (Ty V S)} {past bodySigs : List (Ports (Ty V S))}
    (fn : Function V S) (selector : Origin (context ++ params) past (.control (extra + 2)))
    (ports : Fin (extra + 2) → Port context fn.port)
    (initial : Wires (context ++ params) (past ++ [[fn.port]]) carry)
    (body : LoopBody Op (context ++ FamilyArgs fn extra carry) bodySigs)
    (suffix : NestedTheta.Term (Instruction Op) (context ++ params)
      ((past ++ [[fn.port]]) ++ [context ++ FamilyArgs fn extra carry]) sigs outs) :
    NestedTheta.Term (Instruction Op) (context ++ params) past
      ([fn.port] :: (context ++ FamilyArgs fn extra carry) :: sigs) outs :=
  bindGamma (chooserInputs selector) (chooserArms ports)
    (bindTheta (familyWires fn selector initial) body suffix)

/-- A candidate is a pair of actual typed λ bodies with ordered captures.
The ranked witness separately proves provenance and admissibility. -/
structure CallTarget (m : Machine.{u, v, w} Op) (fn : Function V S) where
  context : Ports (Ty V S)
  sigsL : List (Ports (Ty V S))
  sigsR : List (Ports (Ty V S))
  capturesL : Tuple m.Val context
  capturesR : Tuple m.Val context
  left : NestedTheta.Term (Instruction Op) (context ++ fn.args) [] sigsL fn.results
  right : NestedTheta.Term (Instruction Op) (context ++ fn.args) [] sigsR fn.results

abbrev CallTarget.valueL {fn : Function V S} (target : CallTarget m fn) : m.Val fn.port :=
  .closure target.capturesL target.left.toGraph

abbrev CallTarget.valueR {fn : Function V S} (target : CallTarget m fn) : m.Val fn.port :=
  .closure target.capturesR target.right.toGraph

/-- An ordered region of primitive bindings, static calls, selected γ arms and θ bodies.
Callees decrease rank. Child and suffix plans decrease structurally at the same rank.
A θ activation routes the same static capture prefix into the next feedback activation.
A chooser can forward one of finitely many admitted λs to an application or a θ carry. -/
inductive RankedPlan (m : Machine.{u, v, w} Op) (ids : GlobalRel) :
    Nat → Renaming → {context params outs : Ports (Ty V S)} →
    {past sigsL sigsR : List (Ports (Ty V S))} → Tuple m.Val context → Tuple m.Val context →
    NestedTheta.Term (Instruction Op) (context ++ params) past sigsL outs →
    NestedTheta.Term (Instruction Op) (context ++ params) past sigsR outs → Prop where
  | body {rank : Nat} {map : Renaming} {context params outs : Ports (Ty V S)}
      {sigsL sigsR : List (Ports (Ty V S))} {capturesL capturesR : Tuple m.Val context}
      {left : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsL outs}
      {right : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsR outs}
      (code : CodePair Op map left right) :
    RankedPlan m ids rank map capturesL capturesR left right
  | suffix {rank : Nat} {map : Renaming} {context params outs : Ports (Ty V S)}
      {past sigsL sigsR : List (Ports (Ty V S))} {capturesL capturesR : Tuple m.Val context}
      {left : Term Op (context ++ params) past sigsL outs} {right : Term Op (context ++ params) past sigsR outs}
      (schedule : Local.Schedule Op .identity left right) :
    RankedPlan m ids rank map capturesL capturesR (embed left) (embed right)
  | call {rank calleeRank : Nat} {map : Renaming} {context captured params outs : Ports (Ty V S)}
      {fn : Function V S} {past sigsL sigsR tailL tailR : List (Ports (Ty V S))}
      {capturesL capturesR : Tuple m.Val context} {calleeL calleeR : Tuple m.Val captured}
      {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
      {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
      {suffixL : NestedTheta.Term (Instruction Op) (context ++ params) (past ++ [fn.results]) tailL outs}
      {suffixR : NestedTheta.Term (Instruction Op) (context ++ params) (past ++ [fn.results]) tailR outs}
      (port : Port context fn.port)
      (selectedL : capturesL.get port = .closure calleeL left.toGraph)
      (selectedR : capturesR.get port = .closure calleeR right.toGraph)
      (captured : TupleRelated m ids calleeL calleeR)
      (arguments : Wires (context ++ params) past fn.args)
      (decreases : calleeRank < rank)
      (callee : RankedPlan m ids calleeRank (map.child past.length 0) calleeL calleeR left right)
      (suffix : RankedPlan m ids rank map capturesL capturesR suffixL suffixR) :
    RankedPlan m ids rank map capturesL capturesR
      (bindApplication fn (.cons (.arg (capturePort port)) arguments) suffixL)
      (bindApplication fn (.cons (.arg (capturePort port)) arguments) suffixR)

  | primitive {rank : Nat} {map : Renaming} {context params outs ins head : Ports (Ty V S)}
      {past sigsL sigsR : List (Ports (Ty V S))} {capturesL capturesR : Tuple m.Val context}
      {suffixL : NestedTheta.Term (Instruction Op) (context ++ params) (past ++ [head]) sigsL outs}
      {suffixR : NestedTheta.Term (Instruction Op) (context ++ params) (past ++ [head]) sigsR outs}
      (opcode : Op ins head) (inputs : Wires (context ++ params) past ins)
      (suffix : RankedPlan m ids rank map capturesL capturesR suffixL suffixR) :
    RankedPlan m ids rank map capturesL capturesR (bindPrimitive opcode inputs suffixL) (bindPrimitive opcode inputs suffixR)

  | gamma {rank extra : Nat} {map : Renaming} {context params childContext childArgs returned outs : Ports (Ty V S)}
      {past tailL tailR : List (Ports (Ty V S))} {capturesL capturesR : Tuple m.Val context}
      {sigsL sigsR : Fin (extra + 2) → List (Ports (Ty V S))}
      {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) (childContext ++ childArgs) [] (sigsL i) returned}
      {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) (childContext ++ childArgs) [] (sigsR i) returned}
      {suffixL : NestedTheta.Term (Instruction Op) (context ++ params) (past ++ [returned]) tailL outs}
      {suffixR : NestedTheta.Term (Instruction Op) (context ++ params) (past ++ [returned]) tailR outs}
      (selector : Origin (context ++ params) past (.control (extra + 2)))
      (ports : Tuple (Port context) childContext)
      (arguments : Wires (context ++ params) past childArgs)
      (arms : ∀ i, RankedPlan m ids rank (map.child past.length i.val)
        (projectCaptures capturesL ports) (projectCaptures capturesR ports) (armsL i) (armsR i))
      (suffix : RankedPlan m ids rank map capturesL capturesR suffixL suffixR) :
    RankedPlan m ids rank map capturesL capturesR
      (bindGamma (armInputs selector ports arguments) armsL suffixL)
      (bindGamma (armInputs selector ports arguments) armsR suffixR)


  | theta {rank : Nat} {map : Renaming} {context params bodyContext bodyParams outs : Ports (Ty V S)}
      {past sigsL sigsR tailL tailR : List (Ports (Ty V S))} {capturesL capturesR : Tuple m.Val context}
      {bodyL : LoopBody Op (bodyContext ++ bodyParams) sigsL}
      {bodyR : LoopBody Op (bodyContext ++ bodyParams) sigsR}
      {suffixL : NestedTheta.Term (Instruction Op) (context ++ params) (past ++ [bodyContext ++ bodyParams]) tailL outs}
      {suffixR : NestedTheta.Term (Instruction Op) (context ++ params) (past ++ [bodyContext ++ bodyParams]) tailR outs}
      (ports : Tuple (Port context) bodyContext)
      (initial : Wires (context ++ params) past bodyParams)
      (body : RankedPlan m ids rank (map.child past.length 0)
        (projectCaptures capturesL ports) (projectCaptures capturesR ports) bodyL bodyR)
      (fixedL : PreservesLoopCaptures Op bodyContext bodyParams bodyL)
      (fixedR : PreservesLoopCaptures Op bodyContext bodyParams bodyR)
      (suffix : RankedPlan m ids rank map capturesL capturesR suffixL suffixR) :
    RankedPlan m ids rank map capturesL capturesR
      (bindTheta (captureInputs ports initial) bodyL suffixL)
      (bindTheta (captureInputs ports initial) bodyR suffixR)


  | choose {rank extra : Nat} {map : Renaming} {context params outs : Ports (Ty V S)} {fn : Function V S}
      {past tailL tailR : List (Ports (Ty V S))} {capturesL capturesR : Tuple m.Val context}
      {suffixL : NestedTheta.Term (Instruction Op) (context ++ params) ((past ++ [[fn.port]]) ++ [fn.results]) tailL outs}
      {suffixR : NestedTheta.Term (Instruction Op) (context ++ params) ((past ++ [[fn.port]]) ++ [fn.results]) tailR outs}
      (selector : Origin (context ++ params) past (.control (extra + 2)))
      (ports : Fin (extra + 2) → Port context fn.port)
      (arguments : Wires (context ++ params) (past ++ [[fn.port]]) fn.args)
      (family : Fin (extra + 2) → CallTarget m fn) (ranks : Fin (extra + 2) → Nat)
      (originL : ∀ i, capturesL.get (ports i) = (family i).valueL)
      (originR : ∀ i, capturesR.get (ports i) = (family i).valueR)
      (captured : ∀ i, TupleRelated m ids (family i).capturesL (family i).capturesR)
      (decreases : ∀ i, ranks i < rank)
      (callees : ∀ i, RankedPlan m ids (ranks i) (map.child (past ++ [[fn.port]]).length i.val)
        (family i).capturesL (family i).capturesR (family i).left (family i).right)
      (suffix : RankedPlan m ids rank map capturesL capturesR suffixL suffixR) :
    RankedPlan m ids rank map capturesL capturesR
      (chooseApplication fn selector ports arguments suffixL)
      (chooseApplication fn selector ports arguments suffixR)

  | chooseAfter {rank extra : Nat} {map : Renaming} {context params outs : Ports (Ty V S)} {fn : Function V S}
      {past final steps tailL tailR : List (Ports (Ty V S))} {capturesL capturesR : Tuple m.Val context}
      {suffixL : NestedTheta.Term (Instruction Op) (context ++ params) (final ++ [fn.results]) tailL outs}
      {suffixR : NestedTheta.Term (Instruction Op) (context ++ params) (final ++ [fn.results]) tailR outs}
      (selector : Origin (context ++ params) past (.control (extra + 2)))
      (ports : Fin (extra + 2) → Port context fn.port)
      (route : ChoicePrefix Op (context ++ params) fn (past ++ [[fn.port]]) final steps)
      (arguments : Wires (context ++ params) final fn.args)
      (family : Fin (extra + 2) → CallTarget m fn) (ranks : Fin (extra + 2) → Nat)
      (originL : ∀ i, capturesL.get (ports i) = (family i).valueL)
      (originR : ∀ i, capturesR.get (ports i) = (family i).valueR)
      (captured : ∀ i, TupleRelated m ids (family i).capturesL (family i).capturesR)
      (decreases : ∀ i, ranks i < rank)
      (callees : ∀ i, RankedPlan m ids (ranks i) (map.child final.length i.val)
        (family i).capturesL (family i).capturesR (family i).left (family i).right)
      (suffix : RankedPlan m ids rank map capturesL capturesR suffixL suffixR)
      (ordered : route.Ordered map := by exact True.intro) :
    RankedPlan m ids rank map capturesL capturesR
      (chooseApplicationAfter fn selector ports route arguments suffixL)
      (chooseApplicationAfter fn selector ports route arguments suffixR)

  /-- Check the same scoped body for every admissible selected capture.
  The existing ranked call rule checks descent at each actual application. -/
  | chooseTheta {rank extra : Nat} {map : Renaming}
      {context params carry outs : Ports (Ty V S)} {fn : Function V S}
      {past sigsL sigsR tailL tailR : List (Ports (Ty V S))} {capturesL capturesR : Tuple m.Val context}
      {bodyL : LoopBody Op (fn.port :: carry) sigsL} {bodyR : LoopBody Op (fn.port :: carry) sigsR}
      {suffixL : NestedTheta.Term (Instruction Op) (context ++ params) ((past ++ [[fn.port]]) ++ [fn.port :: carry]) tailL outs}
      {suffixR : NestedTheta.Term (Instruction Op) (context ++ params) ((past ++ [[fn.port]]) ++ [fn.port :: carry]) tailR outs}
      (selector : Origin (context ++ params) past (.control (extra + 2)))
      (ports : Fin (extra + 2) → Port context fn.port)
      (initial : Wires (context ++ params) (past ++ [[fn.port]]) carry)
      (bodies : ∀ i, RankedPlan m ids rank (map.child (past ++ [[fn.port]]).length 0)
        (context := [fn.port]) (params := carry)
        (.cons (capturesL.get (ports i)) .nil) (.cons (capturesR.get (ports i)) .nil) bodyL bodyR)
      (fixedL : PreservesLoopCaptures Op [fn.port] carry bodyL)
      (fixedR : PreservesLoopCaptures Op [fn.port] carry bodyR)
      (suffix : RankedPlan m ids rank map capturesL capturesR suffixL suffixR) :
    RankedPlan m ids rank map capturesL capturesR
      (Gamma.chooseTheta fn selector ports initial bodyL suffixL)
      (Gamma.chooseTheta fn selector ports initial bodyR suffixR)

  /-- One application per θ activation, followed by a γ that can change the
  next member. Each member has its own lower-ranked callee and address map. -/
  | switchTheta {rank extra : Nat} {map : Renaming}
      {context params carry outs : Ports (Ty V S)} {fn : Function V S}
      {past tailL tailR : List (Ports (Ty V S))} {capturesL capturesR : Tuple m.Val context}
      {suffixL : NestedTheta.Term (Instruction Op) (context ++ params)
        ((past ++ [[fn.port]]) ++ [context ++ FamilyArgs fn extra carry]) tailL outs}
      {suffixR : NestedTheta.Term (Instruction Op) (context ++ params)
        ((past ++ [[fn.port]]) ++ [context ++ FamilyArgs fn extra carry]) tailR outs}
      (selector : Origin (context ++ params) past (.control (extra + 2)))
      (ports : Fin (extra + 2) → Port context fn.port)
      (initial : Wires (context ++ params) (past ++ [[fn.port]]) carry)
      (arguments : Wires (context ++ FamilyArgs fn extra carry) [] fn.args)
      (select : Origin (context ++ FamilyArgs fn extra carry) [fn.results] (.control (extra + 2)))
      (feedback : Origin (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]] (.control 2))
      (ordinary : Wires (context ++ FamilyArgs fn extra carry) [fn.results, [fn.port]] carry)
      (family : Fin (extra + 2) → CallTarget m fn) (ranks : Fin (extra + 2) → Nat)
      (originL : ∀ i, capturesL.get (ports i) = (family i).valueL)
      (originR : ∀ i, capturesR.get (ports i) = (family i).valueR)
      (captured : ∀ i, TupleRelated m ids (family i).capturesL (family i).capturesR)
      (decreases : ∀ i, ranks i < rank)
      (callees : ∀ i, RankedPlan m ids (ranks i) ((map.child (past ++ [[fn.port]]).length 0).child 0 i.val)
        (family i).capturesL (family i).capturesR (family i).left (family i).right)
      (suffix : RankedPlan m ids rank map capturesL capturesR suffixL suffixR) :
    RankedPlan m ids rank map capturesL capturesR
      (Gamma.switchTheta fn selector ports initial (familyBody fn ports arguments select feedback ordinary) suffixL)
      (Gamma.switchTheta fn selector ports initial (familyBody fn ports arguments select feedback ordinary) suffixR)

inductive ScheduledLambda (m : Machine.{u, v, w} Op) (ids : GlobalRel) (mapping : Renaming)
    (params outs : Ports (Ty V S)) :
    m.Val (.value (.function params outs)) → m.Val (.value (.function params outs)) → Prop where
  | closure {captured : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {captL captR : Tuple m.Val captured}
      {left : NestedTheta.Term (Instruction Op) (captured ++ params) [] sigsL outs}
      {right : NestedTheta.Term (Instruction Op) (captured ++ params) [] sigsR outs}
      (captures : TupleRelated m ids captL captR) (code : CodePair Op mapping left right) :
    ScheduledLambda m ids mapping params outs (.closure captL left.toGraph) (.closure captR right.toGraph)

  /-- The caller's first capture is the actual paired λ. Its code is
  admitted by call-free `CodePair`. No runtime lookup or target choice
  is used in the witness. Other captures and arguments may feed the call
  and the wiring suffix. -/
  | application {context captured : Ports (Ty V S)} {fn : Function V S}
      {sigsL sigsR : List (Ports (Ty V S))}
      {left : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsL fn.results}
      {right : NestedTheta.Term (Instruction Op) (captured ++ fn.args) [] sigsR fn.results}
      {calleeL calleeR : Tuple m.Val captured} {capturesL capturesR : Tuple m.Val context}
      (calleeCaptures : TupleRelated m ids calleeL calleeR)
      (calleeIso : NestedTheta.Graph.Isomorphic (Instruction Op) left.toGraph right.toGraph)
      (calleeCode : CodePair Op mapping left right)
      (captures : TupleRelated m ids capturesL capturesR)
      (arguments : Wires (fn.port :: (context ++ params)) [] fn.args)
      (outputs : Wires (fn.port :: (context ++ params)) [fn.results] outs) :
    ScheduledLambda m ids mapping params outs
      (.closure (.cons (.closure calleeL left.toGraph) capturesL)
        (applicationCode fn (.cons (.arg .head) arguments) outputs).toGraph)
      (.closure (.cons (.closure calleeR right.toGraph) capturesR)
        (applicationCode fn (.cons (.arg .head) arguments) outputs).toGraph)

  | plan {rank : Nat} {context : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {capL capR : Tuple m.Val context}
      {left : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsL outs}
      {right : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsR outs}
      (scheduled : CallPlan m ids mapping rank capL capR left right) :
    ScheduledLambda m ids mapping params outs (.closure capL left.toGraph) (.closure capR right.toGraph)

  | sequence {rank : Nat} {context : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {capL capR : Tuple m.Val context}
      {left : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsL outs}
      {right : NestedTheta.Term (Instruction Op) (context ++ params) [] sigsR outs}
      (captures : TupleRelated m ids capL capR)
      (scheduled : RankedPlan m ids rank mapping capL capR left right) :
    ScheduledLambda m ids mapping params outs (.closure capL left.toGraph) (.closure capR right.toGraph)

/-- Finite observations and productive feedback at the two call entries.
The original entries are the actual selected closures and post-link store. -/
inductive CallPair (primitives : Primitives m σ) (ids : GlobalRel) (mapping : Renaming)
    (outs : Ports (Ty V S)) : Config m σ outs → Config m σ outs → Prop where
  | returned {sourceL sourceR : Config m σ outs} {valueL valueR : Tuple m.Val outs} {store : σ}
      (values : TupleRelated m ids valueL valueR)
      (ranL : SingleTheta.TerminalOutcome primitives sourceL (.returned valueL store))
      (ranR : SingleTheta.TerminalOutcome primitives sourceR (.returned valueR store)) :
    CallPair primitives ids mapping outs sourceL sourceR
  | blocked {sourceL sourceR : Config m σ outs}
      {args : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {left : NestedTheta.Term (Instruction Op) args [] sigsL outs}
      {right : NestedTheta.Term (Instruction Op) args [] sigsR outs}
      {inputL inputR : Tuple m.Val args} {store : σ} {locL locR : Location} {stopL stopR : Block m σ outs}
      (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR)
      (ranL : SingleTheta.TerminalOutcome primitives sourceL stopL.outcome)
      (ranR : SingleTheta.TerminalOutcome primitives sourceR stopR.outcome) :
    CallPair primitives ids mapping outs sourceL sourceR
  | productive {jobL jobR : Job m outs} {store : σ}
      (run : ProductivePair primitives ids jobL jobR store) :
    CallPair primitives ids mapping outs ⟨Continuation.start jobL, store⟩ ⟨Continuation.start jobR, store⟩

inductive DispatchPair (primitives : Primitives m σ) (ids : GlobalRel) (unitRename : Nat → Nat)
    (mapping : Renaming) (outs : Ports (Ty V S)) :
    Except (Failure m σ) (Config m σ outs) → Except (Failure m σ) (Config m σ outs) → Prop where
  | linkBlocked {unitL unitR vertexL vertexR : Nat} {siteL siteR : Site m}
      (address : unitRename vertexL = vertexR) (identity : ids (unitL, vertexL) (unitR, vertexR))
      (sites : SitesRelated m ids siteL siteR) (store : σ) :
    DispatchPair primitives ids unitRename mapping outs
      (.error ⟨unitL, vertexL, siteL, store⟩) (.error ⟨unitR, vertexR, siteR, store⟩)
  | invoked {sourceL sourceR : Config m σ outs} (calls : CallPair primitives ids mapping outs sourceL sourceR) :
    DispatchPair primitives ids unitRename mapping outs (.ok sourceL) (.ok sourceR)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma

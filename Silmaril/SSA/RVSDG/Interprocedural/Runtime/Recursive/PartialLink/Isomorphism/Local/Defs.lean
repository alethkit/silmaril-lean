module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Invocation.Defs

/-! Ordered partial execution of acyclic regions with explicit local graph addresses. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local

open Continuation.Partial (Primitives Eval Site Config Step)
open Continuation.Descent (Pending)

universe u v w

/-- A primitive's local vertex, under zero or more (γ vertex, arm) pairs. -/
inductive Location where
  | here (vertex : Nat)
  | arm (vertex branch : Nat) (inner : Location)
  deriving DecidableEq, Repr

/-- Local vertex maps are independent at each child region. We retain the maps
because the existing existential isomorphism does not expose them at a site. -/
inductive Renaming where
  | identity
  | region (vertices : Nat ≃ Nat) (children : Nat → Nat → Renaming)

def Renaming.vertices : Renaming → Nat ≃ Nat
  | .identity => Equiv.refl Nat
  | .region f _ => f

def Renaming.child : Renaming → Nat → Nat → Renaming
  | .identity => fun _ _ => .identity
  | .region _ children => children

def Renaming.location (rename : Renaming) : Location → Location
  | .here vertex => .here (rename.vertices vertex)
  | .arm vertex branch inner =>
    .arm (rename.vertices vertex) branch ((rename.child vertex branch).location inner)

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args outs : Ports (Ty V S)} {pastL pastR sigsL sigsR : List (Ports (Ty V S))}

/-- The existing typed graph isomorphism with the bijections recorded.
Entry, exit, labels, edges and child positions are checked as in
`Graph.Isomorphic`. The natural-number extension is observed only on
in-range graph vertices. -/
inductive GraphRenumbered (Op : Dialect.{u, v} (ValueSort V S) S) :
    {argsL argsR outsL outsR : Ports (Ty V S)} →
    {sigsL sigsR : List (Ports (Ty V S))} →
    Renaming → Graph Op argsL [] sigsL outsL → Graph Op argsR [] sigsR outsR → Prop where
  | intro {argsL argsR outsL outsR : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {rename : Renaming} {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}
      (entry : argsL = argsR) (exit : outsL = outsR)
      (ids : Fin sigsL.length ≃ Fin sigsR.length)
      (positions : ∀ i, rename.vertices i.val = (ids i).val)
      (labels : ∀ i, (left.nodes i).label = (right.nodes (ids i)).label)
      (inputs : ∀ i, (left.nodes i).inputs.addresses.map (Address.rename (renameVertex ids)) =
        (right.nodes (ids i)).inputs.addresses)
      (results : left.results.addresses.map (Address.rename (renameVertex ids)) =
        right.results.addresses)
      (children : ∀ i (branch : Fin (left.nodes i).shape.regionCount),
        GraphRenumbered Op (rename.child i.val branch.val) (left.children i branch)
          (right.children (ids i) (Fin.cast (congrArg NodeLabel.arity (labels i)) branch))) :
      GraphRenumbered Op rename left right

/-- An administrative γ whose selected child immediately returns no results.
Its own inputs are scoped wires, and its children attempt no actions. -/
abbrev emptyGamma {entry : Ports (Ty V S)} {past : List (Ports (Ty V S))} {extra : Nat}
    (wires : Wires args past (.control (extra + 2) :: entry)) : Node Op args past [] :=
  ⟨_, .gamma extra, wires, fun _ => []⟩

/-- A sufficient execution-order witness. Pair all primitive actions and
nonempty structural work in spine order, recursively in each γ arm.
Only administrative empty γ vertices may be passed on one side alone.
All paired executable positions and edges use the graph's chosen maps. -/
inductive Schedule (Op : Dialect.{u, v} (ValueSort V S) S) :
    {args outs : Ports (Ty V S)} → {pastL pastR sigsL sigsR : List (Ports (Ty V S))} →
    Renaming → Term Op args pastL sigsL outs → Term Op args pastR sigsR outs → Prop where
  | ret {rename : Renaming} {args outs : Ports (Ty V S)}
      {pastL pastR : List (Ports (Ty V S))} (left : Wires args pastL outs) (right : Wires args pastR outs)
      (edges : left.addresses.map (Address.rename rename.vertices) = right.addresses) :
    Schedule Op rename (.ret left) (.ret right)
  | bind {rename : Renaming} {args outs ins head : Ports (Ty V S)}
      {pastL pastR sigsL sigsR : List (Ports (Ty V S))} (shape : Shape Op ins head)
      (left : Wires args pastL ins) (right : Wires args pastR ins)
      {csL csR : Fin shape.regionCount → List (Ports (Ty V S))}
      {childL : (i : Fin shape.regionCount) → Term Op shape.entry [] (csL i) shape.exit}
      {childR : (i : Fin shape.regionCount) → Term Op shape.entry [] (csR i) shape.exit}
      {restL : Term Op args (pastL ++ [head]) sigsL outs}
      {restR : Term Op args (pastR ++ [head]) sigsR outs}
      (position : rename.vertices pastL.length = pastR.length)
      (edges : left.addresses.map (Address.rename rename.vertices) = right.addresses)
      (arms : ∀ i, Schedule Op (rename.child pastL.length i.val) (childL i) (childR i))
      (rest : Schedule Op rename restL restR) :
    Schedule Op rename (.bind ⟨ins, shape, left, csL⟩ childL restL)
      (.bind ⟨ins, shape, right, csR⟩ childR restR)
  | emptyLeft {rename : Renaming} {args outs entry : Ports (Ty V S)}
      {pastL pastR sigsL sigsR : List (Ports (Ty V S))} {extra : Nat}
      (wires : Wires args pastL (.control (extra + 2) :: entry))
      {restL : Term Op args (pastL ++ [[]]) sigsL outs} {right : Term Op args pastR sigsR outs}
      (rest : Schedule Op rename restL right) :
    Schedule Op rename (.bind (emptyGamma wires) (fun _ => .ret .nil) restL) right
  | emptyRight {rename : Renaming} {args outs entry : Ports (Ty V S)}
      {pastL pastR sigsL sigsR : List (Ports (Ty V S))} {extra : Nat}
      (wires : Wires args pastR (.control (extra + 2) :: entry))
      {left : Term Op args pastL sigsL outs} {restR : Term Op args (pastR ++ [[]]) sigsR outs}
      (rest : Schedule Op rename left restR) :
    Schedule Op rename left (.bind (emptyGamma wires) (fun _ => .ret .nil) restR)

/-- The structural and execution-order checks use the same hierarchical
address map, including at every selected primitive. -/
structure OrderedGraph (rename : Renaming) (left : Graph Op args [] sigsL outs)
    (right : Graph Op args [] sigsR outs) : Prop where
  graph : GraphRenumbered Op rename left right
  schedule : Schedule Op rename left.toTerm right.toTerm

/-- Open the exact node job that `embed` uses at a source binding. -/
def nodeJob {m : Machine.{u, v, w} Op} {past : List (Ports (Ty V S))} {head : Ports (Ty V S)}
    (node : Node Op args past head) (children : Children (Term Op) node)
    (input : Tuple m.Val args) (locals : Locals m.Val past) : Job m head :=
  match node, children with
  | ⟨_, .simple opcode, wires, cs⟩, children =>
    (⟨_, _, opcode, cs, fun i => embed (children i), wires.read input locals⟩ : Site m).job
  | ⟨_, @Shape.gamma _ _ _ entry _ extra, wires, cs⟩, children =>
    let kind : NestedTheta.Kind (Instruction Op) (.control (extra + 2) :: entry) head :=
      .base (.gamma extra)
    .node kind cs (fun i => embed (children i)) (wires.read input locals)

variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {ids : GlobalRel} {primitives : Primitives m σ}

/-- Related values at each binding of one shared typed scope. -/
inductive AlignedLocals (m : Machine.{u, v, w} Op) (ids : GlobalRel) :
    {past : List (Ports (Ty V S))} → Locals m.Val past → Locals m.Val past → Prop where
  | empty : AlignedLocals m ids (past := []) PUnit.unit PUnit.unit
  | snoc {past : List (Ports (Ty V S))} {head : Ports (Ty V S)}
      {left right : Locals m.Val past} {valueL valueR : Tuple m.Val head}
      (locals : AlignedLocals m ids left right) (values : TupleRelated m ids valueL valueR) :
    AlignedLocals m ids (left.snoc valueL) (right.snoc valueR)

/-- An address annotation on an actual blocking derivation. Earlier bindings
use successful `Eval` derivations. Entry into a child records the actual
selector and uses fresh locals. The diagnostic and pending frames are
the machine's existing ones. -/
inductive BlockAt (primitives : Primitives m σ) :
    {args outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    Term Op args past sigs outs → Tuple m.Val args → Locals m.Val past →
    σ → Location → Continuation.Partial.Outcome m σ outs → Prop where
  | here {args outs ins head : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      (opcode : Op ins head) (wires : Wires args past ins) {cs : Fin 0 → List (Ports (Ty V S))}
      {children : (i : Fin 0) → Term Op [] [] (cs i) []}
      {rest : Term Op args (past ++ [head]) sigs outs}
      (input : Tuple m.Val args) (locals : Locals m.Val past) (store : σ)
      (undefined : (primitives.step opcode (wires.read input locals)).run store = _root_.Part.none) :
    BlockAt primitives (.bind ⟨ins, .simple opcode, wires, cs⟩ children rest) input locals store
      (.here past.length)
      (.blocked ⟨ins, head, opcode, cs, fun i => embed (children i), wires.read input locals⟩
        (.bind (embed rest) input locals .empty) store)
  | arm {args outs entry head : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))} {extra : Nat}
      {wires : Wires args past (.control (extra + 2) :: entry)}
      {cs : Fin (extra + 2) → List (Ports (Ty V S))}
      {children : (i : Fin (extra + 2)) → Term Op entry [] (cs i) head}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {input : Tuple m.Val args} {locals : Locals m.Val past} {store stopped : σ}
      {tag : Fin (extra + 2)} {parameters : Tuple m.Val entry} {location : Location}
      {site : Site m} {pending : Pending m site.outs head}
      (selection : wires.read input locals = .cons (.control tag) parameters)
      (child : BlockAt primitives (children tag) parameters PUnit.unit store location (.blocked site pending stopped)) :
    BlockAt primitives (.bind ⟨_, Shape.gamma (Op := Op) (entry := entry) (exit := head) extra, wires, cs⟩ children rest) input locals store
      (.arm past.length tag.val location) (.blocked site (.bind (embed rest) input locals pending) stopped)
  | later {args outs head : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      {node : Node Op args past head} {children : Children (Term Op) node}
      {rest : Term Op args (past ++ [head]) sigs outs}
      {input : Tuple m.Val args} {locals : Locals m.Val past} {store middle : σ}
      {value : Tuple m.Val head} {location : Location} {outcome : Continuation.Partial.Outcome m σ outs}
      (first : Eval primitives (nodeJob node children input locals) store (.returned value middle))
      (more : BlockAt primitives rest input (locals.snoc value) middle location outcome) :
    BlockAt primitives (.bind node children rest) input locals store location outcome

/-- The two actual finite observations of scheduled bodies, including the
address of the primitive when either evaluation blocks. -/
inductive EvaluationPair (primitives : Primitives m σ) (ids : GlobalRel) (rename : Renaming)
    {left : Term Op args pastL sigsL outs} {right : Term Op args pastR sigsR outs}
    (inputL inputR : Tuple m.Val args) (localsL : Locals m.Val pastL) (localsR : Locals m.Val pastR)
    (store : σ) : Continuation.Partial.Outcome m σ outs → Continuation.Partial.Outcome m σ outs → Prop where
  | returned {valueL valueR : Tuple m.Val outs} {finalStore : σ}
      (related : TupleRelated m ids valueL valueR)
      (ranL : Eval primitives (.region (embed left) inputL localsL) store (.returned valueL finalStore))
      (ranR : Eval primitives (.region (embed right) inputR localsR) store (.returned valueR finalStore)) :
    EvaluationPair primitives ids rename (left := left) (right := right) inputL inputR localsL localsR store
      (.returned valueL finalStore) (.returned valueR finalStore)
  | blocked {siteL siteR : Site m} {pendingL : Pending m siteL.outs outs} {pendingR : Pending m siteR.outs outs}
      {stopped : σ} (location : Location) (sites : SitesRelated m ids siteL siteR)
      (ranL : BlockAt primitives left inputL localsL store location (.blocked siteL pendingL stopped))
      (ranR : BlockAt primitives right inputR localsR store (rename.location location) (.blocked siteR pendingR stopped)) :
    EvaluationPair primitives ids rename (left := left) (right := right) inputL inputR localsL localsR store
      (.blocked siteL pendingL stopped) (.blocked siteR pendingR stopped)

/-- Both closures contain actual embedded acyclic graphs. Their captures
are related in port order, and their code shares a checked schedule. -/
inductive ScheduledLambda (m : Machine.{u, v, w} Op) (ids : GlobalRel) (rename : Renaming)
    (params results : Ports (Ty V S)) :
    m.Val (.value (.function params results)) → m.Val (.value (.function params results)) → Prop where
  | closure {context : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {capturesL capturesR : Tuple m.Val context}
      {left : Graph Op (context ++ params) [] sigsL results}
      {right : Graph Op (context ++ params) [] sigsR results}
      (captures : TupleRelated m ids capturesL capturesR)
      (code : OrderedGraph rename left right) :
    ScheduledLambda m ids rename params results
      (.closure capturesL (embed left.toTerm).toGraph) (.closure capturesR (embed right.toTerm).toGraph)

/-- A finite path ending at a terminal configuration of the actual machine. -/
structure TerminalPath (primitives : Primitives m σ) {results : Ports (Ty V S)}
    (source target : Config m σ results) : Prop where
  path : Relation.ReflTransGen (Step primitives) source target
  terminal : ∀ next, ¬ Step primitives target next

/-- The bodies' related finite outcomes are reached from the actual
dispatches. A blocking observation retains the source region address,
the existing typed diagnostic and each invocation's pending stack. -/
inductive CallPair (primitives : Primitives m σ) (ids : GlobalRel) (rename : Renaming)
    (outs : Ports (Ty V S)) : Config m σ outs → Config m σ outs → Prop where
  | invoked {sourceL sourceR : Config m σ outs}
      {args : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}
      {left : Graph Op args [] sigsL outs} {right : Graph Op args [] sigsR outs}
      {inputL inputR : Tuple m.Val args} {store : σ} {outL outR : Continuation.Partial.Outcome m σ outs}
      (code : OrderedGraph rename left right)
      (evaluation : EvaluationPair primitives ids rename (left := left.toTerm) (right := right.toTerm)
        inputL inputR PUnit.unit PUnit.unit store outL outR)
      (machineL : ∀ target, TerminalPath primitives sourceL target ↔ target = outL.atStack .halt)
      (machineR : ∀ target, TerminalPath primitives sourceR target ↔ target = outR.atStack .halt) :
    CallPair primitives ids rename outs sourceL sourceR

/-- Link failure uses the existing δ diagnostic relation. Successful
dispatch uses the body-local renumbering, independent of ω addresses. -/
inductive DispatchPair (primitives : Primitives m σ) (ids : GlobalRel) (unitRename : Nat → Nat)
    (bodyRename : Renaming) (outs : Ports (Ty V S)) :
    Except (Failure m σ) (Config m σ outs) → Except (Failure m σ) (Config m σ outs) → Prop where
  | linkBlocked {unitL unitR vertexL vertexR : Nat} {siteL siteR : Site m}
      (address : unitRename vertexL = vertexR) (identity : ids (unitL, vertexL) (unitR, vertexR))
      (sites : SitesRelated m ids siteL siteR) (store : σ) :
    DispatchPair primitives ids unitRename bodyRename outs
      (.error ⟨unitL, vertexL, siteL, store⟩) (.error ⟨unitR, vertexR, siteR, store⟩)
  | invoked {sourceL sourceR : Config m σ outs} (calls : CallPair primitives ids bodyRename outs sourceL sourceR) :
    DispatchPair primitives ids unitRename bodyRename outs (.ok sourceL) (.ok sourceR)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local

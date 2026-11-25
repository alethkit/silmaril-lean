module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Defs

/-! Finite, store-threading ω linking for acyclic δ initializers. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink

open Continuation.Partial (Primitives Eval Site)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

/-- Embed an acyclic initializer in the invocation syntax. No application
or θ is introduced, and the wires and ordered γ children are preserved. -/
def embed : {args outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    RVSDG.Term Op args past sigs outs → NestedTheta.Term (Instruction Op) args past sigs outs
  | _, _, _, _, .ret wires => .ret wires
  | _, _, _, _, .bind ⟨_, .simple opcode, wires, cs⟩ children rest =>
    .bind ⟨_, .base (.simple (.primitive opcode)), wires, cs⟩
      (fun i => embed (children i)) (embed rest)
  | _, _, _, _, .bind ⟨_, .gamma extra, wires, cs⟩ children rest =>
    .bind ⟨_, .base (.gamma extra), wires, cs⟩
      (fun i => embed (children i)) (embed rest)

/-- Open a δ with its actual typed captures and fresh local bindings. -/
def initializerJob {value : ValueSort V S} (delta : Delta Op args past value)
    (imports : Tuple m.Val args) (locals : Locals m.Val past) : Job m [.value value] :=
  .region (embed delta.initializer.toTerm) (delta.captures.read imports locals) PUnit.unit

/-- The store at the attempted action includes earlier successful effects.
The site contains the selected opcode and its full typed input tuple. -/
structure Failure (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) where
  unitId : Nat
  vertex : Nat
  site : Site m
  store : σ

inductive Outcome (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) :
    Ports (Ty V S) → Type (max u v w) where
  | linked {ports : Ports (Ty V S)} (values : Tuple m.Val ports) (store : σ) : Outcome m σ ports
  | undefined {ports : Ports (Ty V S)} (failure : Failure m σ) : Outcome m σ ports

/-- A δ either provides a global with the new store or reports the
selected primitive and the store at which it was attempted. -/
inductive LinksDelta (primitives : Primitives m σ) (unitId vertex : Nat) {value : ValueSort V S}
    (job : Job m [.value value]) (store : σ) : Outcome m σ [.value (.global value)] → Prop where
  | linked {finalStore : σ} {initialized : Tuple m.Val [.value value]}
      (evaluation : Eval primitives job store (.returned initialized finalStore)) :
    LinksDelta primitives unitId vertex job store
      (.linked (.cons (.global unitId vertex (initialized.get .head)) .nil) finalStore)
  | undefined {stopped : σ} {site : Site m} {pending : Continuation.Descent.Pending m site.outs [.value value]}
      (evaluation : Eval primitives job store (.blocked site pending stopped)) :
    LinksDelta primitives unitId vertex job store (.undefined ⟨unitId, vertex, site, stopped⟩)

/-- Recognize an initializer while retaining the vertex's dependent signature. -/
def IsDelta : {ports : Ports (Ty V S)} → Vertex Op args past ports → Prop
  | _, .delta _ => True
  | _, _ => False

/-- λ and φ reuse total packaging. Only a δ evaluates primitive actions. -/
def LinksVertex (primitives : Primitives m σ) (unitId : Nat)
    (imports : Tuple m.Val args) (locals : Locals m.Val past) :
    {ports : Ports (Ty V S)} → Vertex Op args past ports → σ → Outcome m σ ports → Prop
  | _, .lambda body, store, outcome =>
    outcome = .linked (Recursive.linkVertex m unitId imports locals (.lambda body)) store
  | _, .phi group, store, outcome =>
    outcome = .linked (Recursive.linkVertex m unitId imports locals (.phi group)) store
  | _, .delta delta, store, outcome =>
    LinksDelta primitives unitId past.length (initializerJob delta imports locals) store outcome

/-- A successful vertex extends the typed prefix and supplies the store
for the suffix. A blocked vertex ends linking at once. -/
inductive LinksTable (primitives : Primitives m σ) (unitId : Nat) (imports : Tuple m.Val args)
    (outs : Ports (Ty V S)) :
    {past sigs : List (Ports (Ty V S))} → Locals m.Val past → VertexTable Op args past sigs →
    Wires args (extend past sigs) outs → σ → Outcome m σ outs → Prop where
  | ret {past : List (Ports (Ty V S))} (locals : Locals m.Val past)
      (table : VertexTable Op args past []) (results : Wires args past outs) (store : σ) :
    LinksTable primitives unitId imports outs locals table results store (.linked (results.read imports locals) store)
  | bind {past tail : List (Ports (Ty V S))} {head : Ports (Ty V S)} {locals : Locals m.Val past}
      {table : VertexTable Op args past (head :: tail)} {results : Wires args (extend past (head :: tail)) outs}
      {store middle : σ} {values : Tuple m.Val head} {outcome : Outcome m σ outs}
      (first : LinksVertex primitives unitId imports locals (table 0) store (.linked values middle))
      (more : LinksTable primitives unitId imports outs (locals.snoc values) (fun i => table i.succ)
        results middle outcome) :
    LinksTable primitives unitId imports outs locals table results store outcome
  | stop {past tail : List (Ports (Ty V S))} {head : Ports (Ty V S)} {locals : Locals m.Val past}
      {table : VertexTable Op args past (head :: tail)} {results : Wires args (extend past (head :: tail)) outs}
      {store : σ} {failure : Failure m σ}
      (first : LinksVertex primitives unitId imports locals (table 0) store (.undefined failure)) :
    LinksTable primitives unitId imports outs locals table results store (.undefined failure)

/-- Link a single ω unit with its supplied typed imports. Vertex numbers
in diagnostics use the same order and numbering as the total linker. -/
def Links (primitives : Primitives m σ) (unitId : Nat) (graph : Omega Op args outs sigs)
    (imports : Tuple m.Val args) (store : σ) (outcome : Outcome m σ outs) : Prop :=
  LinksTable primitives unitId imports outs (past := []) PUnit.unit graph.region.vertices graph.region.results store outcome

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink

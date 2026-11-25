module

public import Silmaril.SSA.RVSDG.Interprocedural.Terms.Defs

/-! Executable linking and invocation for nonrecursive translation units. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime

universe u v w

variable {V S : Type u}

/-- Runtime colours retain the callable's typed body and captured values.
Global colours carry a translation-unit/vertex identity and an initialized value. -/
inductive Colour (Op : Dialect.{u, v} (ValueSort V S) S) (Data : V → Type w) (State : S → Type w) :
    Ty V S → Type (max u v w) where
  | data {t : V} (value : Data t) : Colour Op Data State (.value (.data t))
  | state {t : S} (value : State t) : Colour Op Data State (.state t)
  | control {n : Nat} (tag : Fin n) : Colour Op Data State (.control n)
  | global {t : ValueSort V S} (unitId vertex : Nat)
      (value : Colour Op Data State (.value t)) : Colour Op Data State (.value (.global t))
  | closure {params results context : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      (values : Tuple (Colour Op Data State) context)
      (body : NestedTheta.Graph (Instruction Op) (context ++ params) [] sigs results) :
      Colour Op Data State (.value (.function params results))

/-- Only primitive opcodes are supplied by the model. Apply is interpreted by invocation below. -/
structure Machine (Op : Dialect.{u, v} (ValueSort V S) S) where
  Data : V → Type w
  State : S → Type w
  primitive {ins outs : Ports (Ty V S)} :
    Op ins outs → Tuple (Colour Op Data State) ins → Tuple (Colour Op Data State) outs

variable {Op : Dialect.{u, v} (ValueSort V S) S}

abbrev Machine.Val (m : Machine.{u, v, w} Op) := Colour Op m.Data m.State

def Colour.selector {D : V → Type w} {E : S → Type w} {n : Nat} :
    Colour Op D E (.control n) → Fin n
  | .control tag => tag

variable {args ins outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

def evalShape (m : Machine.{u, v, w} Op) :
    {ins outs : Ports (Ty V S)} → (shape : Shape Op ins outs) →
    (Fin shape.regionCount → Tuple m.Val shape.entry → Tuple m.Val shape.exit) →
    Tuple m.Val ins → Tuple m.Val outs
  | _, _, .simple opcode, _, input => m.primitive opcode input
  | _, _, .gamma _, child, .cons tag entry => child tag.selector entry

/-- A δ initializer uses only the total acyclic primitive/γ interpreter. -/
def evalInitializer (m : Machine.{u, v, w} Op) :
    {args outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    RVSDG.Term Op args past sigs outs → Tuple m.Val args → Locals m.Val past → Tuple m.Val outs
  | _, _, _, _, .ret wires, entry, locals => wires.read entry locals
  | _, _, _, _, .bind node children rest, entry, locals =>
    let output := evalShape m node.shape
      (fun i input => evalInitializer m (past := []) (children i) input PUnit.unit)
      (node.inputs.read entry locals)
    evalInitializer m rest entry (locals.snoc output)

abbrev Handler (m : Machine.{u, v, w} Op) :=
  {ins outs : Ports (Ty V S)} → Instruction Op ins outs → Tuple m.Val ins → Option (Tuple m.Val outs)

def evalKind (m : Machine.{u, v, w} Op) (handler : Handler m) (loops : Nat) :
    {ins outs : Ports (Ty V S)} → (kind : NestedTheta.Kind (Instruction Op) ins outs) →
    (Fin kind.arity → Tuple m.Val kind.entry → Option (Tuple m.Val kind.exit)) →
    Tuple m.Val ins → Option (Tuple m.Val outs)
  | _, _, .base (.simple opcode), _, input => handler opcode input
  | _, _, .base (.gamma _), child, .cons tag args => child tag.selector args
  | _, _, .theta _, child, input =>
    NestedTheta.iterate (child (0 : Fin 1)) (fun tag => tag.selector.val == 1) loops input

/-- Open body evaluation. Each call site passes its callable and its arguments
to the supplied instruction handler. Only the selected γ arm runs. -/
def evalBody (m : Machine.{u, v, w} Op) (handler : Handler m) (loops : Nat) :
    {args outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    NestedTheta.Term (Instruction Op) args past sigs outs → Tuple m.Val args →
    Locals m.Val past → Option (Tuple m.Val outs)
  | _, _, _, _, .ret wires, entry, locals => some (wires.read entry locals)
  | _, _, _, _, .bind node children rest, entry, locals => do
    let output ← evalKind m handler loops node.kind
      (fun i input => evalBody m handler loops (past := []) (children i) input PUnit.unit)
      (node.inputs.read entry locals)
    evalBody m handler loops rest entry (locals.snoc output)

abbrev Call (m : Machine.{u, v, w} Op) :=
  {params results : Ports (Ty V S)} →
  m.Val (.value (.function params results)) → Tuple m.Val params → Option (Tuple m.Val results)

def dispatch (m : Machine.{u, v, w} Op) (call : Call m) : Handler m
  | _, _, .primitive op, args => some (m.primitive op args)
  | _, _, .apply _, .cons callee args => call callee args

/-- Invoke an actual closure. The call bound counts the current activation
and decreases for each nested call. The θ bound applies per loop invocation. -/
def invoke (m : Machine.{u, v, w} Op) (loops : Nat) : Nat → Call m
  | 0, _, _, _, _ => none
  | depth + 1, _, _, .closure values body, arguments =>
    evalBody m (dispatch m (invoke m loops depth)) loops (past := [])
      body.toTerm (prependContext arguments values) PUnit.unit

/-- The definition-level linker reads captures in the local environment. A φ
requires a recursive closure environment and is outside this linker. -/
def linkVertex (m : Machine.{u, v, w} Op) (unitId : Nat)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) :
    {outs : Ports (Ty V S)} → Vertex Op args past outs → Option (Tuple m.Val outs)
  | _, .lambda lambda =>
    let closure := Lambda.close Op lambda entry locals
    some (.cons (.closure closure.values closure.body) .nil)
  | _, .delta delta =>
    let values := delta.captures.read entry locals
    let initialized := evalInitializer m (past := []) delta.initializer.toTerm values PUnit.unit
    some (.cons (.global unitId past.length (initialized.get .head)) .nil)
  | _, .phi _ => none

def linkTable (m : Machine.{u, v, w} Op) (unitId : Nat) (imports : Tuple m.Val args) :
    (past sigs : List (Ports (Ty V S))) → Locals m.Val past →
    VertexTable Op args past sigs → Wires args (extend past sigs) outs → Option (Tuple m.Val outs)
  | _, [], locals, _, results => some (results.read imports locals)
  | past, head :: tail, locals, table, results => do
    let value ← linkVertex m unitId imports locals (table 0)
    linkTable m unitId imports (past ++ [head]) tail (locals.snoc value)
      (fun i => table i.succ) results

/-- Link the numbered ω graph with an explicit typed import tuple. -/
def linkGraph (m : Machine.{u, v, w} Op) (unitId : Nat) (graph : Omega Op args outs sigs)
    (imports : Tuple m.Val args) : Option (Tuple m.Val outs) :=
  linkTable m unitId imports [] sigs PUnit.unit graph.region.vertices graph.region.results

def linkBindings (m : Machine.{u, v, w} Op) (unitId : Nat) (imports : Tuple m.Val args) :
    {past sigs : List (Ports (Ty V S))} → ModuleTerm Op args past sigs outs →
    Locals m.Val past → Option (Tuple m.Val outs)
  | _, _, .ret wires, locals => some (wires.read imports locals)
  | _, _, .bind definition rest, locals => do
    let value ← linkVertex m unitId imports locals definition.toGraph
    linkBindings m unitId imports rest (locals.snoc value)

/-- Link a term by visiting its bindings in order. -/
def linkTerm (m : Machine.{u, v, w} Op) (unitId : Nat) (term : OmegaTerm Op args outs sigs)
    (imports : Tuple m.Val args) : Option (Tuple m.Val outs) :=
  linkBindings m unitId imports (past := []) term.region PUnit.unit

/-- This linker admits modules without recursive groups. Calls are checked separately
when their closures execute. -/
def NoPhi : {past sigs : List (Ports (Ty V S))} → ModuleTerm Op args past sigs outs → Prop
  | _, _, .ret _ => True
  | _, _, .bind (.phi _) _ => False
  | _, _, .bind _ rest => NoPhi rest

/-- Resolve an import tuple by explicit typed wires out of a provider's exports. -/
def wireImports (m : Machine.{u, v, w} Op) (wires : Wires outs [] args)
    (exports : Tuple m.Val outs) : Tuple m.Val args :=
  wires.read exports PUnit.unit

end Silmaril.SSA.RVSDG.Interprocedural.Runtime

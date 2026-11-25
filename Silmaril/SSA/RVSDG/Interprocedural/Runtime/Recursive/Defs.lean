module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Defs

/-! φ linking and finite calls through a typed group environment. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

def linkVertex (m : Machine.{u, v, w} Op) (unitId : Nat)
    (imports : Tuple m.Val args) (locals : Locals m.Val past) :
    {outs : Ports (Ty V S)} → Vertex Op args past outs → Tuple m.Val outs
  | _, .lambda lambda => lambdaValue m imports locals lambda
  | _, .delta delta => deltaValue m unitId imports locals delta
  | _, .phi (members := members) group =>
    let outer := group.captures.read imports locals
    memberValues members (Colour.member outer group.definitions)

def linkTable (m : Machine.{u, v, w} Op) (unitId : Nat) (imports : Tuple m.Val args) :
    (past sigs : List (Ports (Ty V S))) → Locals m.Val past →
    VertexTable Op args past sigs → Wires args (extend past sigs) outs → Tuple m.Val outs
  | _, [], locals, _, results => results.read imports locals
  | past, head :: tail, locals, table, results =>
    let values := linkVertex m unitId imports locals (table 0)
    linkTable m unitId imports (past ++ [head]) tail (locals.snoc values)
      (fun i => table i.succ) results

/-- Link φ groups to typed callable references alongside the existing λ and δ cases. -/
def linkGraph (m : Machine.{u, v, w} Op) (unitId : Nat) (graph : Omega Op args outs sigs)
    (imports : Tuple m.Val args) : Tuple m.Val outs :=
  linkTable m unitId imports [] sigs PUnit.unit graph.region.vertices graph.region.results

def linkBindings (m : Machine.{u, v, w} Op) (unitId : Nat) (imports : Tuple m.Val args) :
    {past sigs : List (Ports (Ty V S))} → ModuleTerm Op args past sigs outs →
    Locals m.Val past → Tuple m.Val outs
  | _, _, .ret wires, locals => wires.read imports locals
  | _, _, .bind definition rest, locals =>
    let value := linkVertex m unitId imports locals definition.toGraph
    linkBindings m unitId imports rest (locals.snoc value)

/-- Link the inductive ω syntax, preserving the numbering used for global identities. -/
def linkTerm (m : Machine.{u, v, w} Op) (unitId : Nat) (term : OmegaTerm Op args outs sigs)
    (imports : Tuple m.Val args) : Tuple m.Val outs :=
  linkBindings m unitId imports (past := []) term.region PUnit.unit

abbrev Bodies (kind : NestedTheta.Kind (Instruction Op) args outs)
    (cs : Fin kind.arity → List (Ports (Ty V S))) :=
  (i : Fin kind.arity) → NestedTheta.Term (Instruction Op) kind.entry [] (cs i) kind.exit

/-- The three judgments used by finite call derivations. -/
inductive Job (m : Machine.{u, v, w} Op) : Ports (Ty V S) → Type (max u v w) where
  | call {params results : Ports (Ty V S)}
      (callee : m.Val (.value (.function params results))) (arguments : Tuple m.Val params) :
      Job m results
  | region {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      (body : NestedTheta.Term (Instruction Op) args past sigs outs) (input : Tuple m.Val args)
      (locals : Locals m.Val past) : Job m outs
  | node {ins outs : Ports (Ty V S)} (kind : NestedTheta.Kind (Instruction Op) ins outs)
      (cs : Fin kind.arity → List (Ports (Ty V S))) (children : Bodies kind cs)
      (input : Tuple m.Val ins) : Job m outs

def Job.openClosure (m : Machine.{u, v, w} Op)
    (callee : m.Val (.value (.function args outs))) (arguments : Tuple m.Val args) : Job m outs :=
  let closure := resolve m callee
  .region closure.body.toTerm (Closure.enter Op closure arguments) (PUnit.unit : Locals m.Val [])

/-- Unbounded finite execution with explicit call premises. This slice can
visit primitives, calls and selected γ arms. A reached θ has no rule. -/
inductive Returns (m : Machine.{u, v, w} Op) :
    {outs : Ports (Ty V S)} → Job m outs → Tuple m.Val outs → Prop where
  | call {args outs : Ports (Ty V S)} {callee : m.Val (.value (.function args outs))}
      {arguments : Tuple m.Val args} {output : Tuple m.Val outs}
      (body : Returns m (Job.openClosure m callee arguments) output) :
      Returns m (.call callee arguments) output
  | ret {args outs : Ports (Ty V S)} {past : List (Ports (Ty V S))}
      (wires : Wires args past outs) (input : Tuple m.Val args) (locals : Locals m.Val past) :
      Returns m (.region (.ret wires) input locals) (wires.read input locals)
  | bind {args head outs : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      {node : NestedTheta.Node (Instruction Op) args past head}
      {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail outs}
      {input : Tuple m.Val args} {locals : Locals m.Val past}
      {result : Tuple m.Val head} {output : Tuple m.Val outs}
      (first : Returns m (.node node.kind node.childSigs children (node.inputs.read input locals)) result)
      (more : Returns m (.region rest input (locals.snoc result)) output) :
      Returns m (.region (.bind node children rest) input locals) output
  | primitive {ins outs : Ports (Ty V S)} (opcode : Op ins outs)
      (cs : Fin 0 → List (Ports (Ty V S)))
      (children : (i : Fin 0) → NestedTheta.Term (Instruction Op) [] [] (cs i) [])
      (input : Tuple m.Val ins) :
      Returns m (.node (.base (.simple (.primitive opcode))) cs children input)
        (m.primitive opcode input)
  | apply {fn : Function V S} {cs : Fin 0 → List (Ports (Ty V S))}
      {children : (i : Fin 0) → NestedTheta.Term (Instruction Op) [] [] (cs i) []}
      {callee : m.Val (.value (.function fn.args fn.results))}
      {arguments : Tuple m.Val fn.args} {output : Tuple m.Val fn.results}
      (invocation : Returns m (.call callee arguments) output) :
      Returns m (.node (.base (.simple (.apply fn))) cs children (.cons callee arguments)) output
  | gamma {entry exit : Ports (Ty V S)} {extra : Nat}
      {cs : Fin (extra + 2) → List (Ports (Ty V S))}
      {children : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (cs i) exit}
      {tag : Fin (extra + 2)} {input : Tuple m.Val entry} {output : Tuple m.Val exit}
      (branch : Returns m (.region (children tag) input (PUnit.unit : Locals m.Val [])) output) :
      Returns m (.node (.base (.gamma (entry := entry) (exit := exit) extra))
        cs children (.cons (.control tag) input)) output

/-- The bounded algorithms for the three judgments, with θ budget zero. -/
def Job.run (m : Machine.{u, v, w} Op) (depth : Nat) :
    {outs : Ports (Ty V S)} → Job m outs → Option (Tuple m.Val outs)
  | _, .call callee arguments => invoke m 0 depth callee arguments
  | _, .region body entry locals => evalBody m (dispatch m (invoke m 0 depth)) 0 body entry locals
  | _, .node kind _cs children input =>
    evalKind m (dispatch m (invoke m 0 depth)) 0 kind
      (fun i x => evalBody m (dispatch m (invoke m 0 depth)) 0 (past := []) (children i) x PUnit.unit)
      input

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive

module

public import Silmaril.SSA.RVSDG.Interprocedural.Defs

/-! Inductive bindings for the λ, δ, φ and ω fragment. The graph target is
the existing `Interprocedural.Omega` and its existing structural vertices. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural

universe u v w

/-- A sequence of definitions in member order, with each successive position
carrying its own type. -/
inductive Definitions : {n : Nat} → (Fin n → Type w) → Type (w + 1) where
  | nil {F : Fin 0 → Type w} : Definitions F
  | cons {n : Nat} {F : Fin (n + 1) → Type w} (head : F 0)
      (rest : Definitions (fun i => F i.succ)) : Definitions F

def Definitions.get : {n : Nat} → {F : Fin n → Type w} → Definitions F → (i : Fin n) → F i
  | _, _, .nil, i => i.elim0
  | _, _, .cons head rest, i => Fin.cases head rest.get i

def Definitions.ofTable : (n : Nat) → {F : Fin n → Type w} →
    ((i : Fin n) → F i) → Definitions F
  | 0, _, _ => .nil
  | n + 1, _, table => .cons (table 0) (ofTable n (fun i => table i.succ))

variable {V S : Type u}
variable (Op : Dialect.{u, v} (ValueSort V S) S)

structure LambdaTerm (args : Ports (Ty V S)) (past : List (Ports (Ty V S))) (fn : Function V S) where
  context : Ports (Ty V S)
  captures : Wires args past context
  bodySigs : List (Ports (Ty V S))
  body : NestedTheta.Term (Instruction Op) (context ++ fn.args) [] bodySigs fn.results

structure DeltaTerm (args : Ports (Ty V S)) (past : List (Ports (Ty V S))) (value : ValueSort V S) where
  context : Ports (Ty V S)
  captures : Wires args past context
  bodySigs : List (Ports (Ty V S))
  initializer : RVSDG.Term Op context [] bodySigs [.value value]

structure PhiTerm (args : Ports (Ty V S)) (past : List (Ports (Ty V S))) (members : List (Function V S)) where
  context : Ports (Ty V S)
  captures : Wires args past context
  definitions : Definitions (fun (i : Fin members.length) =>
    LambdaTerm Op (context ++ memberPorts members) (memberOutputs (members.take i.val)) members[i])

/-- The three kinds of bindings in a translation-unit term. -/
inductive VertexTerm (args : Ports (Ty V S)) (past : List (Ports (Ty V S))) :
    Ports (Ty V S) → Type (max u v + 1) where
  | lambda {fn : Function V S} (term : LambdaTerm Op args past fn) : VertexTerm args past [fn.port]
  | delta {value : ValueSort V S} (term : DeltaTerm Op args past value) :
      VertexTerm args past [.value (.global value)]
  | phi {members : List (Function V S)} (term : PhiTerm Op args past members) :
      VertexTerm args past (memberPorts members)

/-- Module syntax consists of lets followed by an ordered export tuple.
Each let extends the available prefix with exactly its own outputs. -/
inductive ModuleTerm (imports : Ports (Ty V S)) :
    (past sigs : List (Ports (Ty V S))) → (exports : Ports (Ty V S)) → Type (max u v + 1) where
  | ret {exports : Ports (Ty V S)} {past : List (Ports (Ty V S))}
      (results : Wires imports past exports) : ModuleTerm imports past [] exports
  | bind {head exports : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      (definition : VertexTerm Op imports past head)
      (rest : ModuleTerm imports (past ++ [head]) tail exports) :
      ModuleTerm imports past (head :: tail) exports

structure OmegaTerm (imports exports : Ports (Ty V S)) (sigs : List (Ports (Ty V S))) where
  region : ModuleTerm Op imports [] sigs exports

variable {Op}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
variable {fn : Function V S} {value : ValueSort V S} {members : List (Function V S)}

def LambdaTerm.toGraph (t : LambdaTerm Op args past fn) : Lambda Op args past fn :=
  ⟨t.context, t.captures, t.bodySigs, t.body.toGraph⟩

def Lambda.toTerm (g : Lambda Op args past fn) : LambdaTerm Op args past fn :=
  ⟨g.context, g.captures, g.bodySigs, g.body.toTerm⟩

def DeltaTerm.toGraph (t : DeltaTerm Op args past value) : Delta Op args past value :=
  ⟨t.context, t.captures, t.bodySigs, t.initializer.toGraph⟩

def Delta.toTerm (g : Delta Op args past value) : DeltaTerm Op args past value :=
  ⟨g.context, g.captures, g.bodySigs, g.initializer.toTerm⟩

def PhiTerm.toGraph (t : PhiTerm Op args past members) : Phi Op args past members :=
  ⟨t.context, t.captures, fun i => (t.definitions.get i).toGraph⟩

def Phi.toTerm (g : Phi Op args past members) : PhiTerm Op args past members :=
  ⟨g.context, g.captures, Definitions.ofTable members.length (fun i => (g.definitions i).toTerm)⟩

def VertexTerm.toGraph : VertexTerm Op args past outs → Vertex Op args past outs
  | .lambda t => .lambda t.toGraph
  | .delta t => .delta t.toGraph
  | .phi t => .phi t.toGraph

def Vertex.toTerm : Vertex Op args past outs → VertexTerm Op args past outs
  | .lambda g => .lambda g.toTerm
  | .delta g => .delta g.toTerm
  | .phi g => .phi g.toTerm

/-- A table view of the unprocessed module suffix. The whole ω graph uses an empty prefix. -/
abbrev VertexTable (Op : Dialect.{u, v} (ValueSort V S) S) (args : Ports (Ty V S))
    (past sigs : List (Ports (Ty V S))) :=
  (i : Fin sigs.length) → Vertex Op args (site past sigs i).1 (site past sigs i).2

def ModuleTerm.vertices :
    {past sigs : List (Ports (Ty V S))} → ModuleTerm Op args past sigs outs →
      VertexTable Op args past sigs
  | _, _, .ret _ => fun i => i.elim0
  | _, _, .bind definition rest => Fin.cases definition.toGraph rest.vertices

def ModuleTerm.results :
    {past sigs : List (Ports (Ty V S))} → ModuleTerm Op args past sigs outs →
      Wires args (extend past sigs) outs
  | _, _, .ret results => results
  | _, _, .bind _ rest => rest.results

def ModuleTerm.fromTable (past : List (Ports (Ty V S))) :
    (sigs : List (Ports (Ty V S))) → VertexTable Op args past sigs →
    Wires args (extend past sigs) outs → ModuleTerm Op args past sigs outs
  | [], _, results => .ret results
  | head :: rest, vertices, results =>
    .bind (vertices 0).toTerm (fromTable (past ++ [head]) rest (fun i => vertices i.succ) results)

def OmegaTerm.toGraph (t : OmegaTerm Op args outs sigs) : Omega Op args outs sigs :=
  ⟨⟨t.region.vertices, t.region.results⟩⟩

def Omega.toTerm (g : Omega Op args outs sigs) : OmegaTerm Op args outs sigs :=
  ⟨ModuleTerm.fromTable [] sigs g.region.vertices g.region.results⟩

end Silmaril.SSA.RVSDG.Interprocedural

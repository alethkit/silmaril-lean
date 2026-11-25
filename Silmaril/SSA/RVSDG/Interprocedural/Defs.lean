module

public import Silmaril.SSA.RVSDG.NestedTheta.Defs

/-! Typed interprocedural RVSDG interfaces from §§4.2.1–4.2.4. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural

universe u v w

/-- The value vocabulary distinguishes callable values and global identities from ordinary data. -/
inductive ValueSort (V S : Type u) where
  | data (sort : V)
  | function (args results : List (PortType (ValueSort V S) S))
  | global (value : ValueSort V S)

abbrev Ty (V S : Type u) := PortType (ValueSort V S) S

structure Function (V S : Type u) where
  args : Ports (Ty V S)
  results : Ports (Ty V S)

variable {V S : Type u}

def Function.port (fn : Function V S) : Ty V S := .value (.function fn.args fn.results)

/-- Application is a simple node with a dedicated tag. Its first operand is the
callable value and the remaining operands are the call arguments. -/
inductive Instruction (Op : Dialect.{u, v} (ValueSort V S) S) :
    Ports (Ty V S) → Ports (Ty V S) → Type (max u v) where
  | primitive {ins outs : Ports (Ty V S)} (opcode : Op ins outs) : Instruction Op ins outs
  | apply (fn : Function V S) : Instruction Op (fn.port :: fn.args) fn.results

variable (Op : Dialect.{u, v} (ValueSort V S) S)

/-- A λ has one function output. Its body receives exactly the context
variables, in capture-port order, followed by the function arguments. -/
structure Lambda (args : Ports (Ty V S)) (past : List (Ports (Ty V S))) (fn : Function V S) where
  context : Ports (Ty V S)
  captures : Wires args past context
  bodySigs : List (Ports (Ty V S))
  body : NestedTheta.Graph (Instruction Op) (context ++ fn.args) [] bodySigs fn.results

/-- Prepend the captured values to the explicit call arguments in boundary-port order. -/
def prependContext {A : Type u} {F : A → Type w} {params : Ports A} (arguments : Tuple F params) :
    {context : Ports A} → Tuple F context → Tuple F (context ++ params)
  | _, .nil => arguments
  | _, .cons x rest => .cons x (prependContext arguments rest)

/-- A closure stores the λ body and the values read from its context inputs. -/
structure Closure (F : Ty V S → Type w) (fn : Function V S) where
  context : Ports (Ty V S)
  values : Tuple F context
  bodySigs : List (Ports (Ty V S))
  body : NestedTheta.Graph (Instruction Op) (context ++ fn.args) [] bodySigs fn.results

def Lambda.close {F : Ty V S → Type w} {args : Ports (Ty V S)}
    {past : List (Ports (Ty V S))} {fn : Function V S}
    (lambda : Lambda Op args past fn) (entry : Tuple F args) (locals : Locals F past) :
    Closure Op F fn :=
  ⟨lambda.context, lambda.captures.read entry locals, lambda.bodySigs, lambda.body⟩

def Closure.enter {F : Ty V S → Type w} {fn : Function V S}
    (closure : Closure Op F fn) (arguments : Tuple F fn.args) :
    Tuple F (closure.context ++ fn.args) :=
  prependContext arguments closure.values

/-- A δ has one global output. Its acyclic initializer receives its context
variables and returns a single right-hand-side value. -/
structure Delta (args : Ports (Ty V S)) (past : List (Ports (Ty V S))) (value : ValueSort V S) where
  context : Ports (Ty V S)
  captures : Wires args past context
  bodySigs : List (Ports (Ty V S))
  initializer : RVSDG.Graph Op context [] bodySigs [.value value]

def memberPorts (members : List (Function V S)) : Ports (Ty V S) :=
  members.map Function.port

def memberOutputs (members : List (Function V S)) : List (Ports (Ty V S)) :=
  members.map (fun fn => [fn.port])

/-- A φ region has context arguments followed by one recursion argument for
each function. The definitions are λ vertices. The result slots read those
vertices' sole outputs in member order, and the enclosing φ exposes that
same tuple. Recursive uses can therefore read the argument ports without
introducing a cycle into the local vertex table. -/
structure Phi (args : Ports (Ty V S)) (past : List (Ports (Ty V S))) (members : List (Function V S)) where
  context : Ports (Ty V S)
  captures : Wires args past context
  definitions : (i : Fin members.length) →
    Lambda Op (context ++ memberPorts members) (memberOutputs (members.take i.val)) members[i]

variable {Op}

/-- Bind context variables before the recursion arguments of a fresh φ region. -/
def Phi.enter {F : Ty V S → Type w} {args : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    {members : List (Function V S)} (phi : Phi Op args past members)
    (entry : Tuple F args) (locals : Locals F past) (recursive : Tuple F (memberPorts members)) :
    Tuple F (phi.context ++ memberPorts members) :=
  prependContext recursive (phi.captures.read entry locals)

/-- A result's exact origin in the φ region. No member can export a different
member's definition, even when both functions have the same type. -/
def Phi.resultOrigin {args : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    {members : List (Function V S)} (phi : Phi Op args past members) (i : Fin members.length) :
    Origin (phi.context ++ memberPorts members) (memberOutputs members) members[i].port := by
  let vertex : Fin (memberOutputs members).length := ⟨i.val, by simp [memberOutputs]⟩
  refine .output vertex ?_
  have same : (memberOutputs members)[vertex] = [members[i].port] :=
    List.getElem_map (fun fn => [fn.port]) (l := members) (i := i.val)
  rw [same]
  exact .head

variable (Op)

/-- Entities in the translation-unit region. Capture edges use the enclosing
prefix; definition and initializer bodies have fresh local scope. -/
inductive Vertex (args : Ports (Ty V S)) (past : List (Ports (Ty V S))) :
    Ports (Ty V S) → Type (max u v) where
  | lambda {fn : Function V S} (node : Lambda Op args past fn) : Vertex args past [fn.port]
  | delta {value : ValueSort V S} (node : Delta Op args past value) :
      Vertex args past [.value (.global value)]
  | phi {members : List (Function V S)} (node : Phi Op args past members) :
      Vertex args past (memberPorts members)

structure ModuleRegion (imports exports : Ports (Ty V S)) (sigs : List (Ports (Ty V S))) where
  vertices : (i : Fin sigs.length) → Vertex Op imports (site [] sigs i).1 (site [] sigs i).2
  results : Wires imports (extend [] sigs) exports

/-- A root ω has no own input or output ports. Its sole region's arguments
are the imports, and its results identify the exports. -/
structure Omega (imports exports : Ports (Ty V S)) (sigs : List (Ports (Ty V S))) where
  region : ModuleRegion Op imports exports sigs

end Silmaril.SSA.RVSDG.Interprocedural

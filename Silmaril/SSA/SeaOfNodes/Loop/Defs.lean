module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs

/-!
# A pure Sea of Nodes single loop

Start enters a Loop Region through its entry occurrence. The Region's If
either exits to Return or takes the one backedge. Every arrival selects
one column of the Region's Phi operands and latches the whole column
simultaneously. Feedback reads the old latch tuple and the shared pure
producers for that activation.

The incoming occurrences correspond to Simple's LoopNode input 1 (entry)
and input 2 (backedge). Simple latches the selected inputs before making
any backedge Phi results visible. This is the Loop Region/Phi rule in
Click and Paleczny, IR ’95 §§2.3 and 3.1–3.2, with a header test so zero
iterations are possible.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Simple chapter 7](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter07/README.md) ·
[Simple chapter 8 evaluator](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L93-L151)

Both producer tables are acyclic and total. The header table can evaluate
its pure producers once before testing the If. There is one return and no
interior control, memory, effects or traps in this profile.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop

open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts sortValue)
open RVSDG (Locals Origin Tuple Wires extend)

universe u v w

/-- The two incoming control occurrences of the Loop Region. -/
inductive Incoming where
  | entry
  | backedge

/-- Select the producer context or operand column for an incoming occurrence. -/
def Incoming.select {α : Type u} (entry backedge : α) : Incoming → α
  | .entry => entry
  | .backedge => backedge

abbrev headerPorts {Data : Type u} (inputs carried : List (ValueSort Data)) :
    List (Ty Data) :=
  dataPorts inputs ++ dataPorts carried

/-- The two columns of Phi operands can have different producer contexts.
The entry column has only the preheader context. The backedge column can
read the current Phi results and the results of the current header table. -/
structure Graph {Data : Type u} (Op : Signature.{u, v} Data)
    (inputs carried : List (ValueSort Data))
    (entrySigs headerSigs : List (List (Ty Data))) (out : ValueSort Data) where
  preheader : Dataflow Op (dataPorts inputs) [] entrySigs
  header : Dataflow Op (headerPorts inputs carried) [] headerSigs
  phiInputs (edge : Incoming) :
    Wires (edge.select (dataPorts inputs) (headerPorts inputs carried))
      (extend [] (edge.select entrySigs headerSigs)) (dataPorts carried)
  predicate : Origin (headerPorts inputs carried) (extend [] headerSigs) (.value .predicate)
  result : Origin (headerPorts inputs carried) (extend [] headerSigs) (.value out)

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable (g : Graph Op inputs carried entrySigs headerSigs out) (m : Model.{u, v, w} Op)

/-- Assemble the header input tuple with the function inputs before the Phi results. -/
def appendTuple {T : Type u} {F : T → Type w} {ys : List T}
    (tail : Tuple F ys) : {xs : List T} → Tuple F xs → Tuple F (xs ++ ys)
  | _, .nil => tail
  | _, .cons x xs => .cons x (appendTuple tail xs)

/-- Read all selected operands from the same immutable producer environment.
An eventual PhiView adapter can supply this occurrence-indexed operand
column while preserving the typed port order and each origin. -/
def Graph.latch (edge : Incoming)
    (args : Tuple (Val m.value) (edge.select (dataPorts inputs) (headerPorts inputs carried)))
    (locals : Locals (Val m.value) (extend [] (edge.select entrySigs headerSigs))) :
    Tuple (Val m.value) (dataPorts carried) :=
  (g.phiInputs edge).read args locals

/-- Fire the preheader and latch the entry column. -/
def Graph.initial (input : Tuple (Val m.value) (dataPorts inputs)) :
    Tuple (Val m.value) (dataPorts carried) :=
  g.latch m .entry input (g.preheader.eval m input PUnit.unit)

/-- Fire the shared header producers on the old latch tuple. The false
projection returns; the true projection latches the backedge column. -/
def Graph.step (input : Tuple (Val m.value) (dataPorts inputs))
    (old : Tuple (Val m.value) (dataPorts carried)) :
    sortValue m.value out ⊕ Tuple (Val m.value) (dataPorts carried) :=
  let args := appendTuple old input
  let locals := g.header.eval m args PUnit.unit
  if (Diamond.read m g.predicate args locals).down then
    .inr (g.latch m .backedge args locals)
  else
    .inl (Diamond.read m g.result args locals)

/-- Finite execution from a latched tuple, counting completed backedges. -/
inductive Graph.ReturnsAfter (input : Tuple (Val m.value) (dataPorts inputs)) :
    Nat → Tuple (Val m.value) (dataPorts carried) → sortValue m.value out → Prop where
  | exit {old result} (taken : g.step m input old = .inl result) :
      ReturnsAfter input 0 old result
  | backedge {count old next result} (taken : g.step m input old = .inr next)
      (rest : ReturnsAfter input count next result) :
      ReturnsAfter input (count + 1) old result

/-- A finite execution from Start returns the given result. -/
def Graph.Returns (input : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out) :
    Prop :=
  ∃ count, g.ReturnsAfter m input count (g.initial m input) result

/-- Once at the header, examine the exit even with a budget of zero. Only
taking a backedge consumes budget. `none` means the budget was exhausted. -/
def Graph.evalFrom (input : Tuple (Val m.value) (dataPorts inputs)) :
    Nat → Tuple (Val m.value) (dataPorts carried) → Option (sortValue m.value out)
  | 0, old => match g.step m input old with
    | .inl result => some result
    | .inr _ => none
  | budget + 1, old => match g.step m input old with
    | .inl result => some result
    | .inr next => evalFrom input budget next

/-- Execute from Start with a budget of completed backedges. -/
def Graph.evalBackedges (budget : Nat) (input : Tuple (Val m.value) (dataPorts inputs)) :
    Option (sortValue m.value out) :=
  g.evalFrom m input budget (g.initial m input)

end Silmaril.SSA.SeaOfNodes.Loop

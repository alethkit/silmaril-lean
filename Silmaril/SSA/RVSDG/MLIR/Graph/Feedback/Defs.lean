module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Stateless.Defs
public import Silmaril.Foundations.InfiniteTrace

/-! # Scoped MLIR-style regions for stateless RVSDG feedback

The block arguments and each operation's ordered results form groups of SSA
names. A nested region opens with only its own block arguments. Operation
bindings are strict, including when every result of an operation is unused.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Feedback

open NestedTheta.Institution
open OrderedRuntime.Structured (Values)

universe u v w
variable {V : Type u} {A : Stateless.Signature.{u,v} V}

abbrev PortSort (V : Type u) := OrderedRuntime.Structured.Ty V

/-- References select a result number within a previously bound group. Group
zero is the block argument tuple. The separate RVSDG argument space is empty. -/
abbrev Operands (scope : List (Ports (PortSort V))) (ports : Ports (PortSort V)) :=
  Wires [] scope ports

/-- A single block with explicit, ordered SSA bindings. Control operations
bind their complete result tuples before the remainder of the block executes. -/
inductive Block (A : Stateless.Signature.{u,v} V) :
    List (Ports (PortSort V)) → Ports (PortSort V) → Type (max u v) where
  | yield {scope outs} (values : Operands scope outs) : Block A scope outs
  | prim {scope ins results outs} (op : A.pure ins results) (args : Operands scope ins)
      (rest : Block A (scope ++ [results]) outs) : Block A scope outs
  | choose {scope params results outs} {extra : Nat}
      (args : Operands scope (.control (extra + 2) :: params))
      (arms : Fin (extra + 2) → Block A [params] results)
      (rest : Block A (scope ++ [results]) outs) : Block A scope outs
  | feedback {scope carried outs} (seed : Operands scope carried)
      (body : Block A [carried] (.control 2 :: carried))
      (rest : Block A (scope ++ [carried]) outs) : Block A scope outs

abbrev Region (A : Stateless.Signature.{u,v} V) (args outs : Ports (PortSort V)) :=
  Block A [args] outs

variable {args outs carried : Ports (PortSort V)} {scope past sigs : List (Ports (PortSort V))}

/-- Number the argument group first, followed by previously bound results. -/
def bindOperands (wires : Wires args past outs) : Operands (args :: past) outs :=
  wires.map fun _ => fun
    | .arg port => .output 0 port
    | .output node port => .output node.succ port

/-- Keep every binding, with isolated regions at the operation's region slots. -/
def emit : {ins results : Ports (PortSort V)} → (kind : NestedTheta.Kind A.op ins results) →
    Operands scope ins → (Fin kind.arity → Region A kind.entry kind.exit) →
    Block A (scope ++ [results]) outs → Block A scope outs
  | _, _, .base (.simple (.pure op)), args, _, rest => .prim op args rest
  | _, _, .base (.simple (.effect op)), _, _, _ => nomatch op
  | _, _, .base (.gamma _), args, regions, rest => .choose args regions rest
  | _, _, .theta _, args, regions, rest => .feedback args (regions (0 : Fin 1)) rest

/-- Resolve numbered wires into block-local SSA references. -/
def lowerTerm : {args outs : Ports (PortSort V)} → {past sigs : List (Ports (PortSort V))} →
    NestedTheta.Term A.op args past sigs outs → Block A (args :: past) outs
  | _, _, _, _, .ret values => .yield (bindOperands values)
  | _, _, _, _, .bind node children rest =>
    emit node.kind (bindOperands node.inputs) (fun r => lowerTerm (children r)) (lowerTerm rest)

/-- Lower a numbered graph admitted by the stateless institution. The entry
arguments and the yielded result tuple retain their declared profiles. -/
def lower (g : NestedTheta.Graph A.op args [] sigs outs)
    (_stateFree : Stateless.NoState g.toTerm) : Region A args outs :=
  lowerTerm g.toTerm

variable {value : V → Type w}

/-- A restart completes the body with selector `1` and passes its entire
updated carry tuple as the next activation's arguments. -/
def Restart (body : Tuple (Values value) carried → Tuple (Values value) (.control 2 :: carried) → Prop)
    (input next : Tuple (Values value) carried) : Prop :=
  body input (.cons ⟨1⟩ next)

/-- The initial body activation is mandatory. A finite return consists of zero
or more completed restarts followed by one completed body with selector `0`. -/
def FeedbackReturns
    (body : Tuple (Values value) carried → Tuple (Values value) (.control 2 :: carried) → Prop)
    (input output : Tuple (Values value) carried) : Prop :=
  ∃ last, Relation.ReflTransGen (Restart body) input last ∧
    body last (.cons ⟨0⟩ output)

/-- The target block semantics executes each binding, then interprets the
terminator in the resulting scope. It observes the whole ordered tuple. -/
def Block.Exec (m : Stateless.Model.{u,v,w} A) :
    {scope : List (Ports (PortSort V))} → {outs : Ports (PortSort V)} → Block A scope outs →
    Locals (Values m.value) scope → Tuple (Values m.value) outs → Prop
  | _, _, .yield values, env, output => values.read .nil env = output
  | _, _, .prim op args rest, env, output =>
    rest.Exec m (env.snoc (m.run op (args.read .nil env))) output
  | _, _, .choose args arms rest, env, output =>
    let .cons selector payload := args.read .nil env
    ∃ result, (arms selector.down).Exec m (payload, PUnit.unit) result ∧
      rest.Exec m (env.snoc result) output
  | _, _, .feedback seed body rest, env, output =>
    ∃ result, FeedbackReturns (fun x y => body.Exec m (x, PUnit.unit) y) (seed.read .nil env) result ∧
      rest.Exec m (env.snoc result) output

def Block.Returns (r : Region A args outs) (m : Stateless.Model.{u,v,w} A)
    (input : Tuple (Values m.value) args) (output : Tuple (Values m.value) outs) : Prop :=
  r.Exec m (input, PUnit.unit) output

/-- A positive witness of productive feedback in a particular body. Each
transition is a successful activation followed by an actual restart. -/
def Productive (body : Region A carried (.control 2 :: carried)) (m : Stateless.Model.{u,v,w} A)
    (input : Tuple (Values m.value) carried) : Prop :=
  InfiniteTrace (Restart (body.Returns m)) input

end Silmaril.SSA.RVSDG.MLIR.Graph.Feedback

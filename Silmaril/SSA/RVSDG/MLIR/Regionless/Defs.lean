module

public import Silmaril.SSA.RVSDG.Institution.Defs
public import Silmaril.SSA.MLIR.Institution.Defs

/-! # From RVSDG value graphs to regionless MLIR equations

A profile map assigns every opcode a regionless symbol with the same ordered
operands and results, reindexed by a single value sort map. Whole graphs also
have value-only boundaries. A first γ vertex would need a control wire from a
graph argument or an earlier primitive result, neither of which can supply one.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.MLIR.Regionless

open CategoryTheory
open Silmaril.MLIR.Institution (Assignment Block OpArity Profile Signature)

variable {V St : Type} {P Q : Dialect V St} {L K : Signature false}

/-- View an ordered list of value sorts as RVSDG ports. -/
def valuePorts (St : Type) (ts : List V) : Ports (PortType V St) :=
  ts.map PortType.value

/-- View a list of sorts as an MLIR context, preserving order and repetitions. -/
def context {Ty : Type} (sort : V → Ty) (ts : List V) : Fin ts.length → Ty :=
  fun i => sort (ts.get i)

/-- The regionless profile for the given ordered value lists. -/
def profile {Ty : Type} (sort : V → Ty) (ins outs : List V) :
    Profile (⟨ins.length, outs.length, ()⟩ : OpArity false) Ty :=
  -- Applying sort at the empty region slots makes postcomposition definitional.
  ⟨context sort ins, context sort outs, (fun r _ => sort r.elim0), (fun r _ => sort r.elim0)⟩

/-- A symbol whose profile witnesses that both RVSDG port lists are value-only. -/
inductive MatchedOp (sort : V → L.Ty) : Dialect V St where
  | symbol {ins outs : List V} (op : L.Op (profile sort ins outs)) :
      MatchedOp sort (valuePorts St ins) (valuePorts St outs)

/-- A typed assignment of regionless MLIR symbols to a value-only RVSDG dialect. -/
structure ProfileMap (P : Dialect V St) (L : Signature false) where
  sort : V → L.Ty
  symbol : Institution.OpcodeMap P (MatchedOp (L := L) sort)

/-- Precompose with an RVSDG opcode relabelling. -/
def ProfileMap.precomp (f : ProfileMap Q L) (h : Institution.OpcodeMap P Q) : ProfileMap P L :=
  ⟨f.sort, fun op => f.symbol (h op)⟩

def MatchedOp.map {sort : V → L.Ty} (k : L ⟶ K) {ins outs : Ports (PortType V St)} :
    MatchedOp (L := L) sort ins outs → MatchedOp (L := K) (k.sort ∘ sort) ins outs
  | .symbol s => .symbol (k.symbol s)

/-- Postcompose with an MLIR signature map, including its action on value sorts. -/
def ProfileMap.map (f : ProfileMap P L) (k : L ⟶ K) : ProfileMap P K :=
  ⟨k.sort ∘ f.sort, fun op => (f.symbol op).map k⟩

/-- Read the components of an RVSDG value tuple by position. -/
def toAssignment {F : PortType V St → Type} :
    (ts : List V) → Tuple F (valuePorts St ts) → (i : Fin ts.length) → F (.value (ts.get i))
  | [], _, i => i.elim0
  | t :: ts, .cons x xs, i => Fin.cases (motive := fun j => F (.value ((t :: ts).get j)))
      x (toAssignment ts xs) i

/-- Assemble a typed RVSDG value tuple in the same order as an assignment. -/
def ofAssignment {F : PortType V St → Type} :
    (ts : List V) → ((i : Fin ts.length) → F (.value (ts.get i))) → Tuple F (valuePorts St ts)
  | [], _ => .nil
  | _ :: ts, env => .cons (env 0) (ofAssignment ts (fun i => env i.succ))

def MatchedOp.interpret {sort : V → L.Ty} {F : PortType V St → Type}
    (run : ∀ {ins outs : List V}, L.Op (profile sort ins outs) →
      ((i : Fin ins.length) → F (.value (ins.get i))) →
      (i : Fin outs.length) → F (.value (outs.get i))) {ins outs : Ports (PortType V St)} :
    MatchedOp (L := L) sort ins outs → Tuple F ins → Tuple F outs
  | .symbol s, input => ofAssignment _ (run s (toAssignment _ input))

/-- Interpret the matched value opcodes on carriers at the MLIR sorts. -/
def ProfileMap.interpret (f : ProfileMap P L) (carrier : L.Ty → Type)
    (run : ∀ {ins outs : List V}, L.Op (profile f.sort ins outs) →
      Assignment carrier (context f.sort ins) → Assignment carrier (context f.sort outs)) :
    Model P where
  value t := carrier (f.sort t)
  state _ := PEmpty
  run op := (f.symbol op).interpret run

/-- Pull a regionless MLIR model back to the matched RVSDG dialect. -/
def ProfileMap.pullback (f : ProfileMap P L) (M : Silmaril.MLIR.Institution.Model L) : Model P :=
  f.interpret M.carrier (fun op args => M.op op args (fun r => r.elim0))

/-- Bind an operation's result slots to expressions over its operand context. -/
def operationBlock {sort : V → L.Ty} {ins outs : List V}
    (op : L.Op (profile sort ins outs)) : Block L (context sort ins) (context sort outs) :=
  fun i => .app op (fun j => .var j) (fun r => r.elim0) i

/-- The RVSDG evaluator can carry expressions in place of values. Each binding
substitutes its resolved operand expressions into every result expression. -/
def ProfileMap.syntaxModel (f : ProfileMap P L) (args : List V) : Model P :=
  f.interpret (Silmaril.MLIR.Institution.Term L (context f.sort args))
    (fun op operands i => (operationBlock (L := L) op i).subst operands)

/-- Translate a numbered graph by resolving its bindings and result wires in the
syntax model, starting with the MLIR variables for the graph arguments. -/
def translateGraph (f : ProfileMap P L) {args outs : List V}
    {sigs : List (Ports (PortType V St))}
    (g : Graph P (valuePorts St args) [] sigs (valuePorts St outs)) :
    Block L (context f.sort args) (context f.sort outs) :=
  toAssignment outs (g.run (f.syntaxModel args) (ofAssignment args Silmaril.MLIR.Institution.Term.var))

/-- The value-boundary fragment of the canonical RVSDG equation type. -/
structure ValueEquation (P : Dialect V St) where
  args : List V
  outs : List V
  leftSigs : List (Ports (PortType V St))
  rightSigs : List (Ports (PortType V St))
  lhs : Graph P (valuePorts St args) [] leftSigs (valuePorts St outs)
  rhs : Graph P (valuePorts St args) [] rightSigs (valuePorts St outs)

/-- Use the original numbered graphs and port lists as an RVSDG sentence. -/
def ValueEquation.toRVSDG (e : ValueEquation P) : Institution.Equation P :=
  ⟨valuePorts St e.args, valuePorts St e.outs, e.leftSigs, e.rightSigs, e.lhs, e.rhs⟩

def ValueEquation.map (e : ValueEquation P) (h : Institution.OpcodeMap P Q) : ValueEquation Q :=
  ⟨e.args, e.outs, e.leftSigs, e.rightSigs, Institution.mapGraph h e.lhs,
    Institution.mapGraph h e.rhs⟩

/-- Translate both sides at the same ordered argument and result contexts. -/
def translateEquation (f : ProfileMap P L) (e : ValueEquation P) : Silmaril.MLIR.Institution.Equation L :=
  ⟨e.args.length, e.outs.length, context f.sort e.args, context f.sort e.outs,
    translateGraph f e.lhs, translateGraph f e.rhs⟩

end Silmaril.SSA.RVSDG.MLIR.Regionless

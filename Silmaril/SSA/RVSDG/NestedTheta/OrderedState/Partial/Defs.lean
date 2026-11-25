module

public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Defs
public import Silmaril.Foundations.InfiniteTrace

/-! # Endpoint observations of partial ordered nested RVSDG -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial

open OrderedRuntime.Structured (Instruction Values Ty)

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args ins outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

/-- Each enclosing region contributes its binding number and selected child
number. An iteration uses the same body site on every activation. -/
abbrev Path := List (Nat × Nat)

/-- A blocked effect records its static site, indexed opcode, actual
arguments, and the exact store at the attempted instruction. -/
structure Block (E : Dialect.{u,v} V PUnit.{u + 1})
    (value : V → Type (max u w)) (σ : Type (max u w)) where
  path : Path
  vertex : Nat
  ins : Ports (Ty V)
  outs : Ports (Ty V)
  opcode : E ins outs
  input : Tuple (Values value) ins
  store : σ

inductive Abnormal (E : Dialect.{u,v} V PUnit.{u + 1})
    (value : V → Type (max u w)) (σ : Type (max u w)) where
  | blocked (attempt : Block E value σ)
  | diverges

abbrev Model (P E : Dialect.{u,v} V PUnit.{u + 1}) (σ : Type (max u w)) :=
  OrderedRuntime.Structured.Model.{u,v,w} P E (StateT σ _root_.Part)

variable (m : Model.{u,v,w} P E σ)

abbrev interpretation : MonadicModel.{u,v,max u w} (Instruction P E) (StateT σ _root_.Part) :=
  ⟨m.value, fun _ => PUnit, m.step⟩

/-- Successful observations are those of the existing nested Elgot
interpretation at the entire tuple and store. -/
noncomputable def runOpen (t : Term (Instruction P E) args past sigs outs)
    (input : Tuple (Values m.value) args) (locals : Locals (Values m.value) past) (store : σ) :
    _root_.Part (Configuration m.value σ outs) :=
  (t.denoteOpenWith (interpretation m) input locals).run store

/-- A successful vertex runs in the existing computation category and
opens a fresh scope for each child. -/
noncomputable def runNode (node : Node (Instruction P E) args past outs)
    (children : Children (Term (Instruction P E)) node)
    (input : Tuple (Values m.value) args) (locals : Locals (Values m.value) past) (store : σ) :
    _root_.Part (Configuration m.value σ outs) :=
  (node.kind.denoteWith (interpretation m)
    (fun i entry => (children i).denoteOpenWith (interpretation m) entry PUnit.unit)
    (node.inputs.read input locals)).run store

/-- A positive restart completes an entire body activation, produces the
continue tag, and supplies the exact next payload and store. -/
def Restart (body : Configuration m.value σ ins →
    _root_.Part (Configuration m.value σ (Theta.BodyResults ins))) :
    Configuration m.value σ ins → Configuration m.value σ ins → Prop :=
  fun x y => OrderedState.tagged true y ∈ body x

/-- A finite chain of successful restarts can reach a blocked or divergent
body. Alternatively infinitely many completed restarts certify divergence. -/
def loopAbnormal {X : Type (max u w)} (restart : X → X → Prop)
    (child : X → Abnormal E m.value σ → Prop) (input : X) (obs : Abnormal E m.value σ) : Prop :=
  (∃ reached, Relation.ReflTransGen restart input reached ∧ child reached obs) ∨
    (obs = .diverges ∧ InfiniteTrace restart input)

def kindAbnormal (path : Path) (vertex : Nat) :
    {ins outs : Ports (Ty V)} → (kind : Kind (Instruction P E) ins outs) →
    (Fin kind.arity → Configuration m.value σ kind.entry →
      _root_.Part (Configuration m.value σ kind.exit)) →
    (Fin kind.arity → Configuration m.value σ kind.entry → Abnormal E m.value σ → Prop) →
    Configuration m.value σ ins → Abnormal E m.value σ → Prop
  | _, _, .base (.simple (.pure _)), _, _, _, _ => False
  | ins, outs, .base (.simple (.effect op)), _, _, (input, store), obs =>
    ¬ ((m.effect op input).run store).Dom ∧ obs = .blocked ⟨path, vertex, ins, outs, op, input, store⟩
  | _, _, .base (.gamma _), _, children, (.cons tag input, store), obs =>
    children tag.down (input, store) obs
  | _, _, .theta _, body, children, input, obs =>
    loopAbnormal m (Restart m (body (0 : Fin 1))) (children (0 : Fin 1)) input obs

/-- Only the current vertex or, after a successful vertex, its continuation
can supply an abnormal endpoint. Branch entry and iteration pass the current
store to the actual selected region. -/
def abnormalAt (path : Path) :
    {args outs : Ports (Ty V)} → {past sigs : List (Ports (Ty V))} →
    Term (Instruction P E) args past sigs outs → Tuple (Values m.value) args →
    Locals (Values m.value) past → σ → Abnormal E m.value σ → Prop
  | _, _, _, _, .ret _, _, _, _, _ => False
  | _, _, past, _, .bind node children rest, input, locals, store, obs =>
    kindAbnormal m path past.length node.kind
      (fun j x => runOpen m (children j) x.1 PUnit.unit x.2)
      (fun j x => abnormalAt (path ++ [(past.length, j.val)]) (children j) x.1 PUnit.unit x.2)
      (node.inputs.read input locals, store) obs ∨
    ∃ middle ∈ runNode m node children input locals store,
      abnormalAt path rest input (locals.snoc middle.1) middle.2 obs

noncomputable def observe (g : Graph (Instruction P E) args [] sigs outs)
    (input : Tuple (Values m.value) args) (store : σ) : _root_.Part (Configuration m.value σ outs) :=
  runOpen m g.toTerm input PUnit.unit store

def abnormal (g : Graph (Instruction P E) args [] sigs outs)
    (input : Tuple (Values m.value) args) (store : σ) (obs : Abnormal E m.value σ) : Prop :=
  abnormalAt m [] g.toTerm input PUnit.unit store obs

end Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial

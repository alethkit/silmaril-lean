module

public import Silmaril.SSA.Peggy.Optimizer.Extension.Defs
public import Silmaril.SSA.Peggy.Bridge.Egg.Defs
public import Silmaril.SSA.PEG.Builder

/-! # Bounded root matching, generation and selection with sorted Egg replay -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Optimizer

open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egg
open Bridge.Egg
open RVSDG (Tuple)

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params : List (PEG.Ty Data)} {out : PEG.Ty Data}
variable {k : Nat} {Γ : Fin k → PEG.Ty Data}

/-- A variable usable as an operand at a specified sort. -/
structure Variable (Γ : Fin k → PEG.Ty Data) (t : PEG.Ty Data) where
  index : Fin k
  sorted : Γ index = t

/-- The generated fragment adds one application, whose operands are bound
vertices. The left pattern can have arbitrary finite depth. -/
inductive Application (P : PEG.InstructionSet.{0,0} Data) (Γ : Fin k → PEG.Ty Data) :
    PEG.Ty Data → Type where
  | app {n : Nat} {w : Fin n → PEG.Ty Data} {t : PEG.Ty Data}
      (symbol : Symbol P n w t) (args : ∀ i, Variable Γ (w i)) : Application P Γ t

def Application.term : {t : PEG.Ty Data} → Application P Γ t → EQ.Term (signature P) Γ t
  | _, .app sym args =>
    .app sym (fun i => (args i).sorted ▸ EQ.Term.var (args i).index)

/-- A supplied schema uses the existing sorted Egg equality guard language. -/
structure Rule (P : PEG.InstructionSet.{0,0} Data) (out : PEG.Ty Data) where
  scope : Nat
  context : Fin scope → PEG.Ty Data
  guards : List (Core.Equality (signature P) context)
  lhs : EQ.Term (signature P) context out
  rhs : Application P context out

def Rule.core (rule : Rule P out) : Core.Rule (signature P) :=
  ⟨rule.scope, rule.context, rule.guards, ⟨out, rule.lhs, rule.rhs.term⟩⟩

def coreRules (rs : List (Rule P out)) : List (Core.Rule (signature P)) :=
  rs.map Rule.core

abbrev Binding (p : Program P params out) (r : Rule P out) :=
  ∀ i, PEG.Ref p.graph.sort (r.context i)

def termSub {p : Program P params out} {r : Rule P out} (binding : Binding p r)
    (i : Fin r.scope) : Term P params (r.context i) :=
  (binding i).typed ▸ encode p.ranked (binding i).id

structure RootMatch (p : Program P params out) (r : Rule P out) where
  binding : Binding p r
  fits : Core.Pattern.instantiate (termSub binding) r.lhs = encodeOutputs p.ranked 0

/-- Enumerate the finite product of the typed choices. A repeated variable
uses the single value at its context slot throughout instantiation. -/
def assignments : {k : Nat} → {F : Fin k → Type} →
    (∀ i, List (F i)) → List (∀ i, F i)
  | 0, _, _ => [fun i => i.elim0]
  | _ + 1, _, choices =>
    (choices 0).flatMap fun x =>
      (assignments (fun i => choices i.succ)).map fun xs => Fin.cases x xs

/-- Discover substitutions by enumerating old vertices at each variable's
sort, then checking the exact unfolded left pattern at the root. -/
def matchRoot [DecidableEq Data] (eqPrim : PrimitiveEq P)
    (p : Program P params out) (r : Rule P out) : List (RootMatch p r) :=
  let choices := fun i : Fin r.scope =>
    (List.finRange p.size).filterMap (fun v => PEG.Ref.check p.graph.sort (r.context i) v.val)
  (assignments choices).filterMap fun binding =>
    (Core.Replay.matchTerm (matchSymbol eqPrim)
      (Core.Pattern.instantiate (termSub (p := p) (r := r) binding) r.lhs)
      (encodeOutputs p.ranked 0)).map fun eq => ⟨binding, eq_of_heq eq.down⟩

def tupleOfFn {F : PEG.Ty Data → Type} :
    (ts : List (PEG.Ty Data)) → (∀ i : Fin ts.length, F ts[i]) → Tuple F ts
  | [], _ => .nil
  | _ :: ts, f => .cons (f 0) (tupleOfFn ts (fun i => f i.succ))

def generate (p : Program P params out) (r : Rule P out) (binding : Binding p r) :
    Option (Program P params out) :=
  match r.rhs with
  | .app (.prim (ins := ins) op) args =>
    Extension.extend p (.op op) (tupleOfFn ins fun i =>
      (args i).sorted ▸ binding (args i).index)
  | .app (.phi t) args =>
    Extension.extend p .phi (tupleOfFn [.bool, t, t] fun i =>
      (args i).sorted ▸ binding (args i).index)

/-- Construct the ordinary Egg rule receipt. Each guard proposes reflexivity
on its instantiated left side. Replay verifies its right endpoint too. -/
def rewriteReceipt (rs : List (Rule P out)) (i : Fin rs.length)
    (δ : ∀ j, Term P params ((rs.get i).context j)) :
    Core.Replay.Receipt (coreRules rs) (context params) out := by
  let index : Fin (coreRules rs).length := ⟨i.val, by simp [coreRules, i.isLt]⟩
  have entry : (coreRules rs).get index = (rs.get i).core := by simp [coreRules, index]
  suffices ∀ (rule : Core.Rule (signature P)), (coreRules rs).get index = rule →
      (∀ j, Term P params (rule.context j)) →
      Core.Replay.Receipt (coreRules rs) (context params) rule.conclusion.sort from
    this _ entry δ
  intro rule eq sub
  subst rule
  exact .rewrite index sub (fun j => .refl (Core.Pattern.instantiate sub
    (((coreRules rs).get index).guards.get j).lhs))

/-- Every scheduled candidate already carries explanations tied to its
actual source and candidate graph roots. -/
structure Candidate (rs : List (Rule P out)) (source : Program P params out) where
  program : Program P params out
  explained : OutputsExplained (coreRules rs) source.ranked program.ranked

namespace Candidate

def identity (rs : List (Rule P out)) (p : Program P params out) : Candidate rs p :=
  ⟨p, fun i => .refl (encodeOutputs p.ranked i)⟩

def trans {rs : List (Rule P out)} {p : Program P params out}
    (first : Candidate rs p) (next : Candidate rs first.program) : Candidate rs p :=
  ⟨next.program, fun i => .trans (first.explained i) (next.explained i)⟩

end Candidate

def propose [DecidableEq Data] (eqPrim : PrimitiveEq P) (rs : List (Rule P out))
    (p : Program P params out) (i : Fin rs.length) (found : RootMatch p (rs.get i)) :
    Option (Candidate rs p) := do
  let next ← generate p (rs.get i) found.binding
  let receipt := rewriteReceipt rs i (termSub found.binding)
  let proof ← checkOutputs eqPrim p.ranked next.ranked
    (fun slot => Fin.cases receipt (fun j => j.elim0) slot)
  pure ⟨next, proof.down⟩

/-- Scan every supplied schema and replay the candidates generated for
its matching substitutions. -/
def discover [DecidableEq Data] (eqPrim : PrimitiveEq P)
    (rs : List (Rule P out)) (p : Program P params out) : List (Candidate rs p) :=
  (List.finRange rs.length).flatMap fun i =>
    (matchRoot eqPrim p (rs.get i)).filterMap (propose eqPrim rs p i)

/-- A bounded closure of checked root rewrites. The budget is the maximum
number of rule steps on a path. Each frontier is generated independently. -/
def explore [DecidableEq Data] (eqPrim : PrimitiveEq P) (rs : List (Rule P out)) :
    Nat → (p : Program P params out) → List (Candidate rs p)
  | 0, p => [Candidate.identity rs p]
  | fuel + 1, p =>
    Candidate.identity rs p :: (discover eqPrim rs p).flatMap fun step =>
      (explore eqPrim rs fuel step.program).map step.trans

/-- Count applications in the unfolded result tree. Variables cost zero.
Repeated uses and unselected arms still count in this static metric. -/
def applications : {t : PEG.Ty Data} → Term P params t → Nat
  | _, .var _ => 0
  | _, .app (n := arity) _ children =>
    1 + ((List.finRange arity).map fun i => applications (children i)).sum

def Program.cost (p : Program P params out) : Nat := applications (encodeOutputs p.ranked 0)

def prefer {rs : List (Rule P out)} {p : Program P params out} (a b : Candidate rs p) :
    Candidate rs p :=
  if b.program.cost < a.program.cost then b else a

def optimize [DecidableEq Data] (eqPrim : PrimitiveEq P) (rs : List (Rule P out))
    (fuel : Nat) (p : Program P params out) : Candidate rs p :=
  (explore eqPrim rs fuel p).foldl prefer (Candidate.identity rs p)

end Silmaril.SSA.Peggy.Optimizer

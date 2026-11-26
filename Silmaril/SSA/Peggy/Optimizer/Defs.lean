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
variable {params results : List (PEG.Ty Data)} {out : PEG.Ty Data}
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

abbrev Binding (p : RankedProgram P params results) (r : Rule P out) :=
  ∀ i, PEG.Ref p.graph.sort (r.context i)

def termSub {p : RankedProgram P params results} {r : Rule P out} (binding : Binding p r)
    (i : Fin r.scope) : Term P params (r.context i) :=
  (binding i).typed ▸ encode p.ranked (binding i).id

structure TermMatch (p : RankedProgram P params results) (r : Rule P out)
    (target : Term P params out) where
  binding : Binding p r
  fits : Core.Pattern.instantiate (termSub binding) r.lhs = target

abbrev RootMatch (p : Program P params out) (r : Rule P out) :=
  TermMatch p r (encodeOutputs p.ranked 0)

/-- Enumerate the finite product of the typed choices. A repeated variable
uses the single value at its context slot throughout instantiation. -/
def assignments : {k : Nat} → {F : Fin k → Type} →
    (∀ i, List (F i)) → List (∀ i, F i)
  | 0, _, _ => [fun i => i.elim0]
  | _ + 1, _, choices =>
    (choices 0).flatMap fun x =>
      (assignments (fun i => choices i.succ)).map fun xs => Fin.cases x xs

/-- Discover substitutions by enumerating existing vertices at each variable's
sort, then checking equality with the exact target term. -/
def matchTarget [DecidableEq Data] (eqPrim : PrimitiveEq P)
    (p : RankedProgram P params results) (r : Rule P out)
    (target : Term P params out) : List (TermMatch p r target) :=
  let choices := fun i : Fin r.scope =>
    (List.finRange p.size).filterMap (fun v => PEG.Ref.check p.graph.sort (r.context i) v.val)
  (assignments choices).filterMap fun binding =>
    (Core.Replay.matchTerm (matchSymbol eqPrim)
      (Core.Pattern.instantiate (termSub (p := p) (r := r) binding) r.lhs)
      target).map fun eq => ⟨binding, eq_of_heq eq.down⟩

def matchRoot [DecidableEq Data] (eqPrim : PrimitiveEq P)
    (p : Program P params out) (r : Rule P out) : List (RootMatch p r) :=
  matchTarget eqPrim p r (encodeOutputs p.ranked 0)

def tupleOfFn {F : PEG.Ty Data → Type} :
    (ts : List (PEG.Ty Data)) → (∀ i : Fin ts.length, F ts[i]) → Tuple F ts
  | [], _ => .nil
  | _ :: ts, f => .cons (f 0) (tupleOfFn ts (fun i => f i.succ))

def instantiateRow (p : RankedProgram P params results) (r : Rule P out)
    (binding : Binding p r) : PEG.Node P params (Fin 0) p.graph.sort out :=
  match r.rhs with
  | .app (.prim (ins := ins) op) args =>
    PEG.Node.ofLabel (.op op) (tupleOfFn ins fun i => (args i).sorted ▸ binding (args i).index)
  | .app (.phi t) args =>
    PEG.Node.ofLabel .phi (tupleOfFn [.bool, t, t] fun i => (args i).sorted ▸ binding (args i).index)

def generate (p : Program P params out) (r : Rule P out) (binding : Binding p r) :
    Option (Program P params out) :=
  let row := instantiateRow p r binding
  Extension.extend p row.label row.args

/-- Construct the ordinary Egg rule receipt for a mapped table. Each guard
proposes reflexivity on its instantiated left side. Replay checks both sides. -/
def mappedReceipt {Entry : Type} (entries : List Entry) (core : Entry → Core.Rule (signature P))
    (i : Fin entries.length) (δ : ∀ j, Term P params ((core (entries.get i)).context j)) :
    Core.Replay.Receipt (entries.map core) (context params) (core (entries.get i)).conclusion.sort := by
  let index : Fin (entries.map core).length := ⟨i.val, by simp [i.isLt]⟩
  have entry : (entries.map core).get index = core (entries.get i) := by simp [index]
  suffices ∀ (rule : Core.Rule (signature P)), (entries.map core).get index = rule →
      (∀ j, Term P params (rule.context j)) →
      Core.Replay.Receipt (entries.map core) (context params) rule.conclusion.sort from
    this _ entry δ
  intro rule eq sub
  subst rule
  exact .rewrite index sub (fun j => .refl (Core.Pattern.instantiate sub
    (((entries.map core).get index).guards.get j).lhs))

def rewriteReceipt (rs : List (Rule P out)) (i : Fin rs.length)
    (δ : ∀ j, Term P params ((rs.get i).context j)) :
    Core.Replay.Receipt (coreRules rs) (context params) out :=
  mappedReceipt rs Rule.core i δ

/-- A ranked candidate with explanations tied to its ordered graph roots. -/
structure CheckedProgram (rules : List (Core.Rule (signature P)))
    (source : RankedProgram P params results) where
  program : RankedProgram P params results
  explained : OutputsExplained rules source.ranked program.ranked

namespace CheckedProgram

variable {rules : List (Core.Rule (signature P))}

def identity (rules : List (Core.Rule (signature P))) (source : RankedProgram P params results) :
    CheckedProgram rules source :=
  ⟨source, fun i => .refl (encodeOutputs source.ranked i)⟩

def trans {source : RankedProgram P params results}
    (first : CheckedProgram rules source) (next : CheckedProgram rules first.program) :
    CheckedProgram rules source :=
  ⟨next.program, fun i => .trans (first.explained i) (next.explained i)⟩

/-- Validate receipts against the actual ordered outputs of two admitted tables. -/
def verify [DecidableEq Data] (eqPrim : PrimitiveEq P)
    (source target : RankedProgram P params results)
    (receipts : ∀ slot : Fin results.length, Core.Replay.Receipt rules
      (context params) results[slot]) : Option (CheckedProgram rules source) :=
  (checkOutputs eqPrim source.ranked target.ranked receipts).map fun proof => ⟨target, proof.down⟩

def search (next : ∀ p : RankedProgram P params results, List (CheckedProgram rules p)) :
    Nat → (p : RankedProgram P params results) → List (CheckedProgram rules p)
  | 0, p => [identity rules p]
  | fuel + 1, p =>
    identity rules p :: (next p).flatMap fun step =>
      (search next fuel step.program).map step.trans

def preferBy (cost : RankedProgram P params results → Nat)
    {source : RankedProgram P params results} (a b : CheckedProgram rules source) :
    CheckedProgram rules source :=
  if cost b.program < cost a.program then b else a

end CheckedProgram

abbrev Candidate (rs : List (Rule P out)) (source : Program P params out) :=
  CheckedProgram (coreRules rs) source

namespace Candidate

def identity (rs : List (Rule P out)) (p : Program P params out) : Candidate rs p :=
  CheckedProgram.identity (coreRules rs) p

def trans {rs : List (Rule P out)} {p : Program P params out}
    (first : Candidate rs p) (next : Candidate rs first.program) : Candidate rs p :=
  CheckedProgram.trans first next

end Candidate

def propose [DecidableEq Data] (eqPrim : PrimitiveEq P) (rs : List (Rule P out))
    (p : Program P params out) (i : Fin rs.length) (found : RootMatch p (rs.get i)) :
    Option (Candidate rs p) := do
  let next ← generate p (rs.get i) found.binding
  let receipt := rewriteReceipt rs i (termSub found.binding)
  CheckedProgram.verify eqPrim p next (fun slot => Fin.cases receipt (fun j => j.elim0) slot)

/-- Scan every supplied schema and replay the candidates generated for
its matching substitutions. -/
def discover [DecidableEq Data] (eqPrim : PrimitiveEq P)
    (rs : List (Rule P out)) (p : Program P params out) : List (Candidate rs p) :=
  (List.finRange rs.length).flatMap fun i =>
    (matchRoot eqPrim p (rs.get i)).filterMap (propose eqPrim rs p i)

/-- A bounded closure of checked root rewrites. The budget is the maximum
number of rule steps on a path. Each frontier is generated independently. -/
def explore [DecidableEq Data] (eqPrim : PrimitiveEq P) (rs : List (Rule P out)) :
    Nat → (p : Program P params out) → List (Candidate rs p) :=
  CheckedProgram.search (discover eqPrim rs)

/-- Count applications in the unfolded result tree. Variables cost zero.
Repeated uses and unselected arms still count in this static metric. -/
def applications : {t : PEG.Ty Data} → Term P params t → Nat
  | _, .var _ => 0
  | _, .app (n := arity) _ children =>
    1 + ((List.finRange arity).map fun i => applications (children i)).sum

def RankedProgram.cost (p : Program P params out) : Nat := applications (encodeOutputs p.ranked 0)

abbrev Program.cost (p : Program P params out) : Nat := RankedProgram.cost p

def prefer {rs : List (Rule P out)} {p : Program P params out} (a b : Candidate rs p) :
    Candidate rs p :=
  CheckedProgram.preferBy Program.cost a b

def optimize [DecidableEq Data] (eqPrim : PrimitiveEq P) (rs : List (Rule P out))
    (fuel : Nat) (p : Program P params out) : Candidate rs p :=
  (explore eqPrim rs fuel p).foldl prefer (Candidate.identity rs p)

end Silmaril.SSA.Peggy.Optimizer

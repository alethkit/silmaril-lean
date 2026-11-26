module

public import Silmaril.SSA.PEG.Simple.Translate

/-! # Checked loop-free PEG reversion

The untrusted plan identifies shared vertices and explicitly places each
φ in a branch. Demand hints expose strict operands of an already demanded
vertex. An arm may additionally use the demand for its own selected root.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result t : Ty Data} {n : Nat}

/-- A finite, single-result scheduling certificate. Vertex numbering is
independent of scheduling order. `reveal` emits no SIMPLE code. -/
inductive Plan (n : Nat) where
  | done
  | reveal (vertex : Fin n) (next : Plan n)
  | bind (vertex : Fin n) (next : Plan n)
  | branch (phi : Fin n) (yes no next : Plan n)

abbrev vars (sort : Fin n → Ty Data) (params : List (Ty Data)) (live : List (Fin n)) :=
  live.map sort ++ params

variable {sort : Fin n → Ty Data} {live : List (Fin n)} {i : Fin n}

def localPort : {live : List (Fin n)} → Port live i → Port (vars sort params live) (sort i)
  | _, .head => .head
  | _, .tail p => .tail (localPort p)

def paramPort (live : List (Fin n)) (p : Port params t) : Port (vars sort params live) t :=
  match live with
  | [] => p
  | _ :: tail => .tail (paramPort tail p)

def refPort (r : Ref sort t) (slot : Port live r.id) : Port (vars sort params live) t :=
  r.typed ▸ localPort slot

def findSlot (i : Fin n) : (live : List (Fin n)) → Option (Port live i)
  | [] => none
  | v :: tail => if h : v = i then some (h ▸ .head) else (findSlot i tail).map Port.tail

/-- A local read for every ordered occurrence of a graph operand. -/
inductive Reads (sort : Fin n → Ty Data) (live : List (Fin n)) :
    {ins : List (Ty Data)} → Tuple (Ref sort) ins → Type u where
  | nil : Reads sort live (.nil)
  | cons {t : Ty Data} {ts : List (Ty Data)} {r : Ref sort t} {rs : Tuple (Ref sort) ts}
      (head : Port live r.id) (tail : Reads sort live rs) : Reads sort live (.cons r rs)

def Reads.check {ins : List (Ty Data)} : (refs : Tuple (Ref sort) ins) → Option (Reads sort live refs)
  | .nil => some .nil
  | .cons r rs =>
    match findSlot r.id live with
    | none => none
    | some head => (check rs).map (.cons head)

def Reads.args {ins : List (Ty Data)} {refs : Tuple (Ref sort) ins} :
    Reads sort live refs → Args P (vars sort params live) ins
  | .nil => .nil
  | .cons (r := r) head tail => .cons (.var (refPort r head)) tail.args

variable (g : Graph P params [result] n 0)

def strictSlots {ins : List (Ty Data)} {out : Ty Data}
    (label : Label P params (Fin 0) ins out) : List (Fin ins.length) :=
  match label with
  | .param _ => []
  | .op _ => List.finRange ins.length
  | .phi => [0]
  | .theta l | .eval l | .pass l => l.elim0

def strictInputs (i : Fin n) : List (Fin n) :=
  (strictSlots (g.node i).label).map fun slot => ((g.node i).arg slot).id

/-- A plan whose graph wiring, lexical scope and demands have been checked.
Each arm returns the corresponding φ operand and inherits the entry locals.
Arm-local bindings stay in that arm. -/
inductive Schedule (g : Graph P params [result] n 0) :
    {t : Ty Data} → Ref g.sort t → (live needed : List (Fin n)) → Type (max u v) where
  | done {t : Ty Data} {root : Ref g.sort t} {live needed : List (Fin n)} (slot : Port live root.id) :
      Schedule g root live needed
  | reveal {t : Ty Data} {root : Ref g.sort t} {live needed : List (Fin n)}
      (i : Fin n) (demanded : i ∈ needed)
      (next : Schedule g root live (strictInputs g i ++ needed)) :
      Schedule g root live needed
  | param {t : Ty Data} {root : Ref g.sort t} {live needed : List (Fin n)}
      (i : Fin n) (demanded : i ∈ needed)
      (slot : Port params (g.sort i)) (row : g.node i = Node.ofLabel (.param slot) .nil)
      (next : Schedule g root (i :: live) needed) : Schedule g root live needed
  | op {t : Ty Data} {root : Ref g.sort t} {live needed : List (Fin n)}
      {ins : List (Ty Data)} (i : Fin n) (demanded : i ∈ needed)
      (instr : P ins (g.sort i)) (refs : Tuple (Ref g.sort) ins)
      (row : g.node i = Node.ofLabel (.op instr) refs) (reads : Reads g.sort live refs)
      (next : Schedule g root (i :: live) needed) : Schedule g root live needed
  | branch {t : Ty Data} {root : Ref g.sort t} {live needed : List (Fin n)}
      (i : Fin n) (demanded : i ∈ needed)
      (guard : Ref g.sort .bool) (yes no : Ref g.sort (g.sort i))
      (row : g.node i = Node.ofLabel .phi (.cons guard (.cons yes (.cons no .nil))))
      (test : Port live guard.id)
      (yesArm : Schedule g yes live (yes.id :: needed))
      (noArm : Schedule g no live (no.id :: needed))
      (next : Schedule g root (i :: live) needed) : Schedule g root live needed

def Plan.check (g : Graph P params [result] n 0) :
    (plan : Plan n) → {t : Ty Data} → (root : Ref g.sort t) → (live needed : List (Fin n)) →
    Option (Schedule g root live needed)
  | .done, _, root, live, _ =>
    match findSlot root.id live with
    | none => none
    | some slot => some (.done slot)
  | .reveal i next, _, root, live, needed => do
    if h : i ∈ needed then
      return .reveal i h (← next.check g root live (strictInputs g i ++ needed))
    else none
  | .bind i next, _, root, live, needed => do
    if h : i ∈ needed then
      match row : g.node i with
      | ⟨_, .param slot, .nil⟩ =>
        return .param i h slot row (← next.check g root (i :: live) needed)
      | ⟨_, .op instr, refs⟩ =>
        match Reads.check (live := live) refs with
        | none => none
        | some reads => return .op i h instr refs row reads (← next.check g root (i :: live) needed)
      | _ => none
    else none
  | .branch i yesPlan noPlan next, _, root, live, needed => do
    if h : i ∈ needed then
      match row : g.node i with
      | ⟨_, .phi, .cons guard (.cons yes (.cons no .nil))⟩ =>
        match findSlot guard.id live with
        | none => none
        | some test =>
          return .branch i h guard yes no row test
            (← yesPlan.check g yes live (yes.id :: needed))
            (← noPlan.check g no live (no.id :: needed))
            (← next.check g root (i :: live) needed)
      | _ => none
    else none

variable {g}

/-- Each assignment or branch join has one writer site. -/
def Schedule.bindings : {t : Ty Data} → {root : Ref g.sort t} → {live needed : List (Fin n)} →
    Schedule g root live needed → List (Fin n)
  | _, _, _, _, .done _ => []
  | _, _, _, _, .reveal _ _ next => next.bindings
  | _, _, _, _, .param i _ _ _ next | _, _, _, _, .op i _ _ _ _ _ next => i :: next.bindings
  | _, _, _, _, .branch i _ _ _ _ _ _ yes no next =>
    i :: (yes.bindings ++ no.bindings ++ next.bindings)

def keepEntry {vs : List (Ty Data)} {out tmp : Ty Data}
    (step : Stmt P false vs (tmp :: vs)) (next : Stmt P false (tmp :: vs) (out :: tmp :: vs)) :
    Stmt P false vs (out :: vs) :=
  .seq step (.seq next (.project (.cons .head ((ports vs).map fun _ p => .tail (.tail p)))))

/-- Compile each scheduled binding once. Both branch arms project to their
selected result followed by the original entry context. -/
def Schedule.lower : {t : Ty Data} → {root : Ref g.sort t} → {live needed : List (Fin n)} →
    Schedule g root live needed →
    Stmt P false (vars g.sort params live) (t :: vars g.sort params live)
  | _, root, _, _, .done slot => .project (.cons (refPort root slot) (ports _))
  | _, _, _, _, .reveal _ _ next => next.lower
  | _, _, live, _, .param _ _ p _ next =>
    keepEntry (.assign (.var (paramPort live p))) next.lower
  | _, _, _, _, .op _ _ instr _ _ reads next => keepEntry (.assign (.op instr reads.args)) next.lower
  | _, _, _, _, .branch _ _ guard _ _ _ slot yes no next =>
    keepEntry (.branch (.var (refPort guard slot)) yes.lower no.lower) next.lower

def returnRef (g : Graph P params [result] n 0) : Ref g.sort result := g.roots.get .head

/-- The recursive premises of Figure 19 at depth zero in an empty
assumption context. The typed node table already enforces each local
Type-Param, Type-Op and Type-Phi rule and the types of the return boundary. -/
inductive DepthZero (g : Graph P params [result] n 0) : Fin n → Prop where
  | node {i : Fin n} (args : ∀ slot : Fin (g.node i).inputs.length,
      DepthZero g ((g.node i).arg slot).id) : DepthZero g i

/-- A checked admission witness for the single-result, depth-zero fragment.
The rank covers every operand, including operands of vertices omitted by
the plan. Global uniqueness of writer sites enforces static sharing. -/
structure Certificate (g : Graph P params [result] n 0) where
  rank : Fin n → Nat
  ordered : DemandRank.check [.phase rank] g = true
  schedule : Schedule g (returnRef g) [] [(returnRef g).id]
  shared : schedule.bindings.Nodup

def Certificate.check (g : Graph P params [result] n 0) (rank : Fin n → Nat) (plan : Plan n) :
    Option (Certificate g) := do
  if ordered : DemandRank.check [.phase rank] g = true then
    let schedule ← plan.check g (returnRef g) [] [(returnRef g).id]
    if shared : schedule.bindings.Nodup then
      return ⟨rank, ordered, schedule, shared⟩
    else none
  else none

def Certificate.revert (cert : Certificate g) : Program P false params result :=
  ⟨result :: params, cert.schedule.lower, .head⟩

end Silmaril.SSA.PEG.Simple.Revert

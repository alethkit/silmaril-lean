module

public import Silmaril.SSA.PEG.Simple.Graph

/-! # Type-directed loop-free SIMPLE translation

A node context maps each source variable to a typed PEG slot. Sequencing
threads this context, assignment binds a new reference, and both branches
start with the entry context. A φ node selects each live result using one
shared guard. Parameter slots and repeated reads keep the same references.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params nodes vars outs : List (Ty Data)} {out : Ty Data}

def ports : (ts : List (Ty Data)) → Tuple (Port ts) ts
  | [] => .nil
  | _ :: ts => .cons .head ((ports ts).map fun _ p => .tail p)

/-- Emit one parameter node per selected input slot. -/
def paramNodes : {outs : List (Ty Data)} → Tuple (Port params) outs → Build P params nodes outs
  | _, .nil => .keep .nil
  | _, .cons slot rest =>
    let tail := paramNodes rest
    ⟨_, .emit tail.code (.param slot) .nil, .cons .head (tail.refs.map fun _ p => .tail p)⟩

mutual

def Expr.lower : {out : Ty Data} → Expr P vars out → {nodes : List (Ty Data)} →
    Tuple (Port nodes) vars → Build P params nodes [out]
  | _, .var p, _, ctx => .keep (.cons (ctx.get p) .nil)
  | _, .op instr args, _, ctx =>
    let lowered := Args.lower args ctx
    ⟨_, .emit lowered.code (.op instr) lowered.refs, .cons .head .nil⟩

def Args.lower : {outs : List (Ty Data)} → Args P vars outs → {nodes : List (Ty Data)} →
    Tuple (Port nodes) vars → Build P params nodes outs
  | _, .nil, _, _ => .keep .nil
  | _, .cons e es, _, ctx =>
    let head := Expr.lower e ctx
    let tail := Args.lower es (head.code.liftRefs ctx)
    ⟨_, head.code.append tail.code,
      .cons (tail.code.lift (head.refs.get .head)) tail.refs⟩

end

/-- Join the two node contexts in the order of the shared control boundary. -/
def phiNodes (guard : Port nodes .bool) :
    {outs : List (Ty Data)} → Tuple (Port nodes) outs → Tuple (Port nodes) outs →
      Build P params nodes outs
  | _, .nil, .nil => .keep .nil
  | _, .cons y ys, .cons n ns =>
    let tail := phiNodes guard ys ns
    let refs := Tuple.cons (tail.code.lift guard)
      (.cons (tail.code.lift y) (.cons (tail.code.lift n) .nil))
    ⟨_, .emit tail.code .phi refs, .cons .head (tail.refs.map fun _ p => .tail p)⟩

def Stmt.lower {vars outs : List (Ty Data)} (stmt : Stmt P false vars outs)
    {nodes : List (Ty Data)} (ctx : Tuple (Port nodes) vars) : Build P params nodes outs :=
  match stmt with
  | .assign rhs =>
    let lowered := rhs.lower ctx
    ⟨_, lowered.code, .cons (lowered.refs.get .head) (lowered.code.liftRefs ctx)⟩
  | .project slots => .keep (select ctx slots)
  | .seq first second =>
    let a := first.lower ctx
    a.thenBuild (second.lower a.refs)
  | .branch guard yes no =>
    let c := guard.lower ctx
    let entry := c.code.liftRefs ctx
    let y := yes.lower entry
    let n := no.lower (y.code.liftRefs entry)
    let selected := phiNodes (n.code.lift (y.code.lift (c.refs.get .head)))
      (n.code.liftRefs y.refs) n.refs
    c.thenBuild (y.thenBuild (n.thenBuild selected))
  | .while impossible _ _ => nomatch impossible
termination_by structural stmt

def Program.lower (p : Program P false params out) : Build P params [] [out] :=
  let input := paramNodes (ports params)
  let body := p.body.lower input.refs
  input.thenBuild ⟨body.nodes, body.code, .cons (body.refs.get p.retvar) .nil⟩

/-- The result is an ordinary finite PEG with one observable root. -/
def Program.translate (p : Program P false params out) :
    Graph P params [out] p.lower.nodes.length 0 :=
  p.lower.code.toGraph p.lower.refs

end Silmaril.SSA.PEG.Simple

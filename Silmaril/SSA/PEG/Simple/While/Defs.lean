module

public import Silmaril.SSA.PEG.Simple.Translate

/-! # A top-level SIMPLE while with a loop-free guard and body

The parameters are the initial carried store. All slots are carried around
the back edge, and the designated slot is observed at exit.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params vars outs left right nodes base all ins : List (Ty Data)} {out t : Ty Data}

def Stmt.enableWhile : {vars outs : List (Ty Data)} → Stmt P false vars outs → Stmt P true vars outs
  | _, _, .assign e => .assign e
  | _, _, .project slots => .project slots
  | _, _, .seq a b => .seq a.enableWhile b.enableWhile
  | _, _, .branch e a b => .branch e a.enableWhile b.enableWhile
  | _, _, .while impossible _ _ => nomatch impossible

structure WhileProgram (P : InstructionSet.{u,v} Data) (params : List (Ty Data)) (result : Ty Data) where
  guard : Expr P params .bool
  body : Stmt P false params params
  retvar : Port params result

def WhileProgram.source (p : WhileProgram P params out) : Program P true params out :=
  ⟨params, .while rfl p.guard p.body.enableWhile, p.retvar⟩

/-- Emit the guard and body over the same carried references. The first
result is the guard; the remaining results are the next carried store. -/
def WhileProgram.core (p : WhileProgram P params out) : Build P params params (.bool :: params) :=
  let guard := p.guard.lower (params := params) (ports params)
  let body := p.body.lower (params := params) (guard.code.liftRefs (ports params))
  ⟨body.nodes, guard.code.append body.code,
    .cons (body.code.lift (guard.refs.get .head)) body.refs⟩

def portLeft : {left : List (Ty Data)} → Port left out → Port (left ++ right) out
  | _ :: _, .head => .head
  | _ :: _, .tail p => .tail (portLeft p)

def portRight (left : List (Ty Data)) (p : Port right out) : Port (left ++ right) out :=
  match left with
  | [] => p
  | _ :: rest => .tail (portRight rest p)

def portSplit : (left : List (Ty Data)) → {out : Ty Data} →
    Port (left ++ right) out → Port left out ⊕ Port right out
  | [], _, p => .inr p
  | _ :: _, _, .head => .inl .head
  | _ :: rest, _, .tail p => (portSplit rest p).map Port.tail id

/-- A typed graph row where operands are positions in the final table. -/
structure WhileRow (P : InstructionSet.{u,v} Data) (params nodes : List (Ty Data)) (out : Ty Data) where
  inputs : List (Ty Data)
  label : Label P params (Fin 1) inputs out
  refs : Tuple (Port nodes) inputs

/-- Close acyclic code over supplied rows for the holes in its entry context. -/
def Code.closeRows (holes : ∀ {t}, Port base t → WhileRow P params all t) :
    {nodes : List (Ty Data)} → Code P params base nodes →
    (∀ {t}, Port nodes t → Port all t) → Port nodes out → WhileRow P params all out
  | _, .empty, _, p => holes p
  | _, .emit _ label refs, embed, .head =>
    ⟨_, label.map (fun op => op) Fin.elim0, refs.map fun _ r => embed (.tail r)⟩
  | _, .emit prior _ _, embed, .tail p => prior.closeRows holes (fun r => embed (.tail r)) p

def WhileProgram.layout (p : WhileProgram P params out) : List (Ty Data) :=
  out :: .count :: .bool :: (p.core.nodes ++ params)

def WhileProgram.localRef (p : WhileProgram P params out) (r : Port p.core.nodes t) :
    Port p.layout t :=
  .tail (.tail (.tail (portLeft r)))

def WhileProgram.paramRef (p : WhileProgram P params out) (r : Port params t) :
    Port p.layout t :=
  .tail (.tail (.tail (portRight p.core.nodes r)))

def WhileProgram.thetaRow (p : WhileProgram P params out) (r : Port params t) :
    WhileRow P params p.layout t :=
  ⟨_, .theta 0, .cons (p.paramRef r) (.cons (p.localRef (p.core.refs.get (.tail r))) .nil)⟩

def WhileProgram.tailRow (p : WhileProgram P params out)
    (r : Port (p.core.nodes ++ params) t) : WhileRow P params p.layout t :=
  match portSplit p.core.nodes r with
  | .inl q => p.core.code.closeRows (p.thetaRow ·) (p.localRef ·) q
  | .inr q => ⟨_, .param q, .nil⟩

def portConsCases {F : Ty Data → Type w} (head : F t)
    (tail : ∀ {s}, Port nodes s → F s) : {s : Ty Data} → Port (t :: nodes) s → F s
  | _, .head => head
  | _, .tail r => tail r

def WhileProgram.row (p : WhileProgram P params out) (neg : P [.bool] .bool) :
    {t : Ty Data} → Port p.layout t → WhileRow P params p.layout t :=
  portConsCases
    ⟨_, .eval 0, .cons (p.localRef (p.core.code.lift p.retvar)) (.cons (.tail .head) .nil)⟩
    (portConsCases ⟨_, .pass 0, .cons (.tail (.tail .head)) .nil⟩
      (portConsCases ⟨_, .op neg, .cons (p.localRef (p.core.refs.get .head)) .nil⟩
        (p.tailRow ·)))

/-- Ordinary numbered PEG with a single loop. The supplied opcode implements
the exit-test negation under the interpretation used for preservation. -/
def WhileProgram.translate (p : WhileProgram P params out) (neg : P [.bool] .bool) :
    Graph P params [out] p.layout.length 1 where
  forest := ⟨fun _ => none⟩
  sort i := p.layout[i]
  node i :=
    let r := p.row neg (portAt p.layout i)
    .ofLabel r.label (r.refs.map fun _ q => numberPort q)
  roots := .cons (numberPort Port.head) .nil

def WhileProgram.rank (p : WhileProgram P params out) : DemandRank p.layout.length 1 :=
  [.phase (fun i => 3 - i.val), .counter 0, .phase (fun i => p.layout.length - i.val)]

end Silmaril.SSA.PEG.Simple

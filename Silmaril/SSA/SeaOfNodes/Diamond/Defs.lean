module

public import Silmaril.SSA.RVSDG.Defs

/-!
# A single Sea of Nodes control diamond

The graph represents a finite acyclic pure subset. Entry control leads to one IF.
Its two control projections lead directly to one Region. One Phi reads the
Region and its predecessor-keyed operands, and the sole Return reads the Region
and the Phi. The fixed control shape makes these edges implicit in the types of
the corresponding fields. The data edges are explicit typed producer addresses.
Pure total producers can feed either arm and can be shared by any number of users.

The Region and Phi input positions correspond one for one, as in Click and
Paleczny's IR ’95 paper §§2.1–2.4 and §3.1 (figures 3 and 5) and Click's
dissertation §§A.4.2–A.4.3 (figure A.14).
[IR ’95 proceedings](https://doi.org/10.1145/202530.202534) ·
[Rice dissertation](https://hdl.handle.net/1911/16807)

Our Region slots first and second correspond to Simple's slots 1 and 2.
Simple's separate If projection numbers, 0 for true and 1 for false, become
γ arm numbers. The Region may list those projections in either order.
[Simple chapter 5](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter05/README.md) ·
[Branch-and-Phi example](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter05/src/test/java/com/seaofnodes/simple/Chapter05Test.java#L11-L24)

The finite return relation uses the slot of the actual incoming control
predecessor, as Simple's evaluator does when latching the Phi value.
[Simple evaluator](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L113-L151)

We admit Boolean predicates, unpinned pure total dataflow, and one returned Phi.
The dataflow table can be evaluated once in dependency order before dispatch.
Loops, nested control, pinned or effectful operators, and arbitrary scheduling
are outside this fragment.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond

open RVSDG (PortType Port Tuple Origin Wires Locals extend)

universe u v w

/-- The predicate sort is distinguished from the user-selected data sorts. -/
inductive ValueSort (Data : Type u) where
  | predicate
  | data (sort : Data)

abbrev Ty (Data : Type u) := PortType (ValueSort Data) PEmpty.{u+1}
abbrev dataPorts {Data : Type u} (sorts : List (ValueSort Data)) : List (Ty Data) :=
  sorts.map PortType.value

/-- Pure primitives take data operands and have one data result. -/
abbrev Signature (Data : Type u) := List (ValueSort Data) → ValueSort Data → Type v

def sortValue {Data : Type u} (value : Data → Type w) : ValueSort Data → Type w
  | .predicate => ULift.{w} Bool
  | .data sort => value sort

abbrev Val {Data : Type u} (value : Data → Type w) : Ty Data → Type w :=
  PortType.Val (sortValue value) (fun e => nomatch e)

structure Model {Data : Type u} (Op : Signature.{u, v} Data) where
  value : Data → Type w
  run {ins : List (ValueSort Data)} {out : ValueSort Data} :
    Op ins out → Tuple (Val value) (dataPorts ins) → sortValue value out

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}

/-- A topologically enumerated table of data vertices. Wires name arguments or
earlier vertices, so edges are typed and acyclic by construction. -/
inductive Dataflow (Op : Signature.{u, v} Data) (args : List (Ty Data)) :
    List (List (Ty Data)) → List (List (Ty Data)) → Type (max u v) where
  | nil {past : List (List (Ty Data))} : Dataflow Op args past []
  | cons {past sigs : List (List (Ty Data))} {ins : List (ValueSort Data)} {out : ValueSort Data}
      (op : Op ins out) (inputs : Wires args past (dataPorts ins))
      (rest : Dataflow Op args (past ++ [[.value out]]) sigs) :
      Dataflow Op args past ([.value out] :: sigs)

/-- The two distinct control edges out of the unique If vertex. -/
inductive Projection where
  | onTrue
  | onFalse
  deriving DecidableEq

def Projection.ofBool : Bool → Projection
  | true => .onTrue
  | false => .onFalse

inductive Projection.Taken : Bool → Projection → Prop where
  | onTrue : Taken true .onTrue
  | onFalse : Taken false .onFalse

/-- A Region predecessor position, distinct from an If projection number. -/
inductive Slot where
  | first
  | second

/-- Both projections enter this Region exactly once. The first predecessor
determines the order, and the second is the opposite projection. -/
structure Merge where
  first : Projection

def Merge.predecessor (merge : Merge) : Slot → Projection
  | .first => merge.first
  | .second => match merge.first with
    | .onTrue => .onFalse
    | .onFalse => .onTrue

def Merge.slot (merge : Merge) (projection : Projection) : Slot :=
  if projection = merge.first then .first else .second

/-- One Phi attached to this Region, with a same-sort operand at each
Region predecessor position. -/
structure Phi (args : List (Ty Data)) (past : List (List (Ty Data))) (out : ValueSort Data) where
  merge : Merge
  operand : Slot → Origin args past (.value out)

/-- The admitted graphs. Entry feeds the If, the If's projections feed the
Phi's Region, and Return observes the selected Phi operand. -/
structure Graph (Op : Signature.{u, v} Data) (inputs : List (ValueSort Data))
    (sigs : List (List (Ty Data))) (out : ValueSort Data) where
  dataflow : Dataflow Op (dataPorts inputs) [] sigs
  predicate : Origin (dataPorts inputs) (extend [] sigs) (.value .predicate)
  phi : Phi (dataPorts inputs) (extend [] sigs) out

variable (m : Model.{u, v, w} Op)

def read {t : Ty Data} (wire : Origin args past t) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) : Val m.value t :=
  (Wires.read (.cons wire .nil) entry locals).get .head

def Dataflow.eval (entry : Tuple (Val m.value) args) :
    {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs →
      Locals (Val m.value) past → Locals (Val m.value) (extend past sigs)
  | _, _, .nil, locals => locals
  | _, _, .cons op wires rest, locals =>
    rest.eval entry (locals.snoc (.cons (m.run op (wires.read entry locals)) .nil))

/-- A finite derivation fires each shared data producer once. -/
inductive Dataflow.Fires (entry : Tuple (Val m.value) args) :
    {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs →
      Locals (Val m.value) past → Locals (Val m.value) (extend past sigs) → Prop where
  | nil {past : List (List (Ty Data))} {locals : Locals (Val m.value) past} : Fires entry .nil locals locals
  | cons {past sigs : List (List (Ty Data))} {ins : List (ValueSort Data)} {out : ValueSort Data}
      {op : Op ins out} {wires : Wires args past (dataPorts ins)}
      {rest : Dataflow Op args (past ++ [[.value out]]) sigs}
      {locals : Locals (Val m.value) past} {final : Locals (Val m.value) (extend (past ++ [[.value out]]) sigs)}
      (tail : Fires entry rest
        (locals.snoc (Tuple.cons (F := Val m.value) (t := PortType.value out)
          (m.run op (wires.read entry locals)) .nil)) final) :
      Fires entry (.cons op wires rest) locals final

variable {inputs : List (ValueSort Data)} {out : ValueSort Data}

/-- A run follows the taken If projection into the matching Region input
and returns the Phi operand at that input position. -/
inductive Graph.Returns (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) : sortValue m.value out → Prop where
  | ret {locals : Locals (Val m.value) (extend [] sigs)} {projection : Projection} {slot : Slot}
      (data : g.dataflow.Fires m entry PUnit.unit locals)
      (branch : Projection.Taken (read m g.predicate entry locals).down projection)
      (arrival : g.phi.merge.predecessor slot = projection) :
      Returns g entry (read m (g.phi.operand slot) entry locals)

/-- Denotation by composing the pure dataflow with predecessor selection. -/
def Graph.denote (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) : sortValue m.value out :=
  let locals := g.dataflow.eval m entry PUnit.unit
  let projection := Projection.ofBool (read m g.predicate entry locals).down
  read m (g.phi.operand (g.phi.merge.slot projection)) entry locals

/-! ## Lowering to an acyclic RVSDG -/

/-- The only synthetic primitive encodes the predicate as a γ tag and
forwards both Phi operands in Region order. -/
inductive Opcode (Op : Signature.{u, v} Data) : RVSDG.Dialect.{u, max u v} (ValueSort Data) PEmpty.{u+1} where
  | pure {ins : List (ValueSort Data)} {out : ValueSort Data} :
      Op ins out → Opcode Op (dataPorts ins) [.value out]
  | dispatch (out : ValueSort Data) :
      Opcode Op [.value .predicate, .value out, .value out] [.control 2, .value out, .value out]

def Projection.arm : Projection → Fin 2
  | .onTrue => 0
  | .onFalse => 1

abbrev Model.toRVSDG : RVSDG.Model.{u, max u v, w} (Opcode Op) where
  value := sortValue m.value
  state := fun e => nomatch e
  run
    | .pure op, input => .cons (m.run op input) .nil
    | .dispatch _, .cons b operands => .cons ⟨(Projection.ofBool b.down).arm⟩ operands

def Dataflow.lower {results : List (Ty Data)} {tail : List (List (Ty Data))} :
    {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs →
      RVSDG.Term (Opcode Op) args (extend past sigs) tail results →
      RVSDG.Term (Opcode Op) args past (sigs ++ tail) results
  | _, _, .nil, rest => rest
  | _, _, .cons op inputs more, rest =>
    .bind ⟨_, .simple (.pure op), inputs, fun j => j.elim0⟩ (fun j => j.elim0)
      (more.lower rest)

/-- An address of the last producer in a nonempty prefix, expressed using
the same prefix decomposition as the RVSDG local store. -/
def lastIndex (head : List (Ty Data)) :
    (past : List (List (Ty Data))) → Fin (past ++ [head]).length
  | [] => (0 : Fin 1)
  | _ :: tail => (lastIndex head tail).succ

def lastPort {head : List (Ty Data)} {t : Ty Data} (p : Port head t) :
    (past : List (List (Ty Data))) → Port (past ++ [head])[lastIndex head past] t
  | [] => p
  | _ :: tail => lastPort p tail

def lastWires {head : List (Ty Data)} (past : List (List (Ty Data))) {ports : List (Ty Data)}
    (ps : Tuple (Port head) ports) : Wires args (past ++ [head]) ports :=
  ps.map (fun _ p => .output (lastIndex head past) (lastPort p past))

def Slot.port : Slot → Port ([.value out, .value out] : List (Ty Data)) (.value out)
  | .first => .head
  | .second => .tail .head

/-- A γ arm returns the capture at the Region position of this projection. -/
def arm (merge : Merge) (p : Projection) :
    RVSDG.Term (Opcode Op) [.value out, .value out] [] [] [.value out] :=
  .ret (.cons (.arg (merge.slot p).port) .nil)

def arms (merge : Merge) (i : Fin 2) :
    RVSDG.Term (Opcode Op) [.value out, .value out] [] [] [.value out] :=
  Fin.cases (arm merge .onTrue) (fun _ => arm merge .onFalse) i

/-- Only one γ is generated. Its two inputs after the tag are the Phi
operands in Region order, while its children are in If projection order. -/
def Phi.lower (phi : Phi args past out) (predicate : Origin args past (.value .predicate)) :
    RVSDG.Term (Opcode Op) args past [[.control 2, .value out, .value out], [.value out]] [.value out] :=
  .bind ⟨_, .simple (.dispatch out),
      .cons predicate (.cons (phi.operand .first) (.cons (phi.operand .second) .nil)),
      fun j => j.elim0⟩ (fun j => j.elim0)
    (.bind ⟨_, .gamma 0, lastWires past (.cons .head (.cons (.tail .head) (.cons (.tail (.tail .head)) .nil))),
        fun _ => []⟩
      (arms phi.merge)
      (.ret (lastWires (past ++ [[.control 2, .value out, .value out]]) (.cons .head .nil))))

def Graph.lowerTerm (g : Graph Op inputs sigs out) :
    RVSDG.Term (Opcode Op) (dataPorts inputs) []
      (sigs ++ [[.control 2, .value out, .value out], [.value out]]) [.value out] :=
  g.dataflow.lower (g.phi.lower g.predicate)

def Graph.lower (g : Graph Op inputs sigs out) :
    RVSDG.Graph (Opcode Op) (dataPorts inputs) []
      (sigs ++ [[.control 2, .value out, .value out], [.value out]]) [.value out] :=
  g.lowerTerm.toGraph

end Silmaril.SSA.SeaOfNodes.Diamond

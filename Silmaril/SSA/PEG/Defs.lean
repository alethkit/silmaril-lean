module

public import Mathlib.Logic.Equiv.Defs
public import Silmaril.SSA.RVSDG.Defs

/-!
# Typed Program Expression Graphs

A node has one typed result and an ordered list of typed operands. An operand
can name any vertex in the finite table, including a later vertex or the
node itself. Branch selection and loop operators are distinct from the
instruction alphabet. See Tate, Stepp, Tatlock and Lerner, *Equality
Saturation: A New Approach to Optimization*, §5.1 and Fig. 11.
-/

@[expose] public section

namespace Silmaril.SSA.PEG

open RVSDG (Port Tuple)

universe u v w

/-- The control sort and iteration-count sort are independent of the dialect. -/
inductive Ty (Data : Type u) where
  | bool
  | count
  | data (ty : Data)
  deriving DecidableEq

abbrev InstructionSet (Data : Type u) := List (Ty Data) → Ty Data → Type v

abbrev InstructionMap {Data : Type u} (P : InstructionSet.{u,v} Data)
    (Q : InstructionSet.{u,w} Data) := ∀ {ins out}, P ins out → Q ins out

/-- Vertex address with its declared result sort. -/
structure Ref {Data : Type u} {n : Nat} (sort : Fin n → Ty Data) (out : Ty Data) where
  id : Fin n
  typed : sort id = out

def Ref.ofId {Data : Type u} {n : Nat} (sort : Fin n → Ty Data) (i : Fin n) :
    Ref sort (sort i) := ⟨i, rfl⟩

/-- Enumerating a new table in an old table's order determined by `ids`
sends references in the opposite direction. -/
def Ref.reindex {Data : Type u} {n n' : Nat} {sort : Fin n → Ty Data}
    {out : Ty Data} (ids : Fin n' ≃ Fin n) (r : Ref sort out) : Ref (sort ∘ ids) out :=
  ⟨ids.symm r.id, (congrArg sort (ids.apply_symm_apply r.id)).trans r.typed⟩

/-- The role of a dependency matters even when two argument slots name the
same vertex. A feedback edge requires a strictly earlier iteration. -/
inductive EdgeKind (Loop : Type) where
  | ordinary
  | initial (loop : Loop)
  | feedback (loop : Loop)
  | sample (loop : Loop)
  | index (loop : Loop)
  deriving DecidableEq

def EdgeKind.map {L L' : Type} (f : L → L') : EdgeKind L → EdgeKind L'
  | .ordinary => .ordinary
  | .initial l => .initial (f l)
  | .feedback l => .feedback (f l)
  | .sample l => .sample (f l)
  | .index l => .index (f l)

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {Q : InstructionSet.{u,w} Data}
variable {params : List (Ty Data)} {L L' : Type} {ins : List (Ty Data)} {out : Ty Data}

/-- The label determines the ordered input profile and result sort. -/
inductive Label (P : InstructionSet.{u,v} Data) (params : List (Ty Data)) (Loop : Type) :
    List (Ty Data) → Ty Data → Type (max u v) where
  | param {out : Ty Data} (slot : Port params out) : Label P params Loop [] out
  | op {ins : List (Ty Data)} {out : Ty Data} (instr : P ins out) : Label P params Loop ins out
  | phi {out : Ty Data} : Label P params Loop [.bool, out, out] out
  | theta {out : Ty Data} (loop : Loop) : Label P params Loop [out, out] out
  | eval {out : Ty Data} (loop : Loop) : Label P params Loop [out, .count] out
  | pass (loop : Loop) : Label P params Loop [.bool] .count

def Label.map (f : InstructionMap P Q) (loops : L → L') :
    Label P params L ins out → Label Q params L' ins out
  | .param p => .param p
  | .op instr => .op (f instr)
  | .phi => .phi
  | .theta l => .theta (loops l)
  | .eval l => .eval (loops l)
  | .pass l => .pass (loops l)

def Label.kind (label : Label P params L ins out) (slot : Fin ins.length) : EdgeKind L :=
  match label with
  | .theta l => if slot.val = 0 then .initial l else .feedback l
  | .eval l => if slot.val = 0 then .sample l else .index l
  | .pass l => .sample l
  | _ => .ordinary

/-- Loop identifiers of θ, eval and pass labels. -/
def Label.loop : Label P params L ins out → Option L
  | .theta l | .eval l | .pass l => some l
  | _ => none

def Label.thetaLoop : Label P params L ins out → Option L
  | .theta l => some l
  | _ => none

variable {n n' : Nat} {sort : Fin n → Ty Data}

structure Node (P : InstructionSet.{u,v} Data) (params : List (Ty Data)) (Loop : Type)
    {n : Nat} (sort : Fin n → Ty Data) (out : Ty Data) where
  inputs : List (Ty Data)
  label : Label P params Loop inputs out
  args : Tuple (Ref sort) inputs

def Node.ofLabel (label : Label P params L ins out) (args : Tuple (Ref sort) ins) :
    Node P params L sort out := ⟨ins, label, args⟩

/-- The typed port corresponding to a numeric operand position. -/
def portAt : (ts : List (Ty Data)) → (i : Fin ts.length) → Port ts ts[i]
  | [], i => i.elim0
  | _ :: ts, i => Fin.cases .head (fun j => .tail (portAt ts j)) i

def Node.arg (node : Node P params L sort out) (i : Fin node.inputs.length) :
    Ref sort node.inputs[i] := node.args.get (portAt node.inputs i)

def Node.relabel (node : Node P params L sort out) (f : InstructionMap P Q)
    (ids : Fin n' ≃ Fin n) (loops : L → L') : Node Q params L' (sort ∘ ids) out :=
  ⟨node.inputs, node.label.map f loops, node.args.map (fun _ r => r.reindex ids)⟩

/-- A table of loop parents. Scope checks use the parent relation, so loops
at the same depth can have distinct identities. -/
structure LoopForest (n : Nat) where
  parent : Fin n → Option (Fin n)

def LoopForest.reindex {l l' : Nat} (forest : LoopForest l) (ids : Fin l' ≃ Fin l) :
    LoopForest l' := ⟨fun i => (forest.parent (ids i)).map ids.symm⟩

structure Graph (P : InstructionSet.{u,v} Data) (params results : List (Ty Data))
    (nodes loops : Nat) where
  forest : LoopForest loops
  sort : Fin nodes → Ty Data
  node : (i : Fin nodes) → Node P params (Fin loops) sort (sort i)
  roots : Tuple (Ref sort) results

variable {results outputs : List (Ty Data)} {l l' : Nat}

def Graph.withRoots (g : Graph P params results n l) (roots : Tuple (Ref g.sort) outputs) :
    Graph P params outputs n l := ⟨g.forest, g.sort, g.node, roots⟩

/-- Dependencies point from a consumer to its argument. -/
def Graph.Edge (g : Graph P params results n l) (a : Fin n) (kind : EdgeKind (Fin l))
    (b : Fin n) : Prop :=
  ∃ i : Fin (g.node a).inputs.length,
    (g.node a).label.kind i = kind ∧ ((g.node a).arg i).id = b

def Graph.relabel (g : Graph P params results n l) (f : InstructionMap P Q)
    (ids : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) : Graph Q params results n' l' where
  forest := g.forest.reindex loops
  sort := g.sort ∘ ids
  node i := (g.node (ids i)).relabel f ids loops.symm
  roots := g.roots.map (fun _ r => r.reindex ids)

def Graph.mapOps (g : Graph P params results n l) (f : InstructionMap P Q) :
    Graph Q params results n l := g.relabel f (Equiv.refl _) (Equiv.refl _)

def Graph.reindex (g : Graph P params results n l) (ids : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) :
    Graph P params results n' l' := g.relabel (fun op => op) ids loops

end Silmaril.SSA.PEG

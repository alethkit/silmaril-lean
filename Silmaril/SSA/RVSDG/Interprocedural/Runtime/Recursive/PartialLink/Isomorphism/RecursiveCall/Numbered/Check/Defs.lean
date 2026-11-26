module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Check.Labels.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Check.Labels

/-! A proof-producing scan of numbered tables under a supplied renaming. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open Local (Renaming)
open NestedTheta.Equality (OpcodeCode kindCode kind_injective)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op}
variable {args outs : Ports (Ty V S)} {pastL pastR sigsL sigsR : List (Ports (Ty V S))}

theorem instructionKey_injective (code : OpcodeCode Op)
    {ins outs : Ports (Ty V S)} {left right : Instruction Op ins outs}
    (equal : instructionKey code left = instructionKey code right) : left = right :=
  eq_of_heq (Proofs.instructionKey_injective code rfl rfl equal)

/-- Use the dialect's faithful opcode code and a separate application
tag. A typed application label carries its complete signature. -/
def instructionCode (code : OpcodeCode Op) : OpcodeCode (Instruction Op) where
  Key := Sum code.Key (Ports (Ty V S) × Ports (Ty V S))
  encode := instructionKey code
  injective := fun _ _ equal => instructionKey_injective code equal

inductive EmptyHead (Op : Dialect.{u, v} (ValueSort V S) S) :
    {args outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    Code Op args past sigs outs → Type (max u v) where
  | intro {args entry outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))} {extra : Nat}
      (wires : Wires args past (.control (extra + 2) :: entry))
      (rest : Code Op args (past ++ [[]]) sigs outs) :
      EmptyHead Op (.bind (emptyGamma wires) (fun _ => .ret .nil) rest)

theorem emptyRegion {entry : Ports (Ty V S)} (body : Code Op entry [] [] []) :
    body = .ret .nil := by
  cases body with | ret wires => cases wires; rfl

variable [DecidableEq (Ty V S)]

def emptyHead :
    {args outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    (term : Code Op args past sigs outs) → Option (EmptyHead Op term)
  | _, _, _, _, .bind ⟨_, .base (.gamma (exit := head) _), wires, cs⟩ children rest => by
    by_cases empty : head = []
    · subst head
      refine if rows : ∀ i, cs i = [] then ?_ else none
      have same := funext rows
      subst cs
      have arms := funext fun i => emptyRegion (children i)
      subst children
      exact some (.intro wires rest)
    · exact none
  | _, _, _, _, _ => none

def termSize :
    {args outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    Code Op args past sigs outs → Nat
  | _, _, _, _, .ret _ => 1
  | _, _, _, _, .bind _ children rest =>
    1 + termSize rest + (List.ofFn (fun i => termSize (children i))).sum
termination_by structural _ _ _ _ term => term

def scan (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] :
    Nat → (mapping : Renaming) →
    {args outs : Ports (Ty V S)} → {pastL pastR sigsL sigsR : List (Ports (Ty V S))} →
    (left : Code Op args pastL sigsL outs) → (right : Code Op args pastR sigsR outs) →
    Option (PLift (Ordered Op mapping left.toGraph right.toGraph))
  | 0, _, _, _, _, _, _, _, _, _ => none
  | budget + 1, mapping, _, _, _, _, _, _, left, right =>
    match emptyHead left with
    | some (.intro wires rest) => (scan keys budget mapping rest right).map fun cert =>
      ⟨.emptyLeft wires cert.down⟩
    | none =>
      match emptyHead right with
      | some (.intro wires rest) => (scan keys budget mapping left rest).map fun cert =>
        ⟨.emptyRight wires cert.down⟩
      | none =>
        match left, right with
        | .ret l, .ret r =>
          if edges : l.addresses.map (Address.rename mapping.vertices) = r.addresses then
            some ⟨.ret l r edges⟩
          else none
        | .bind (past := preL) (head := headL) ⟨insL, kindL, l, _⟩ childrenL restL,
          .bind (past := preR) (head := headR) ⟨insR, kindR, r, _⟩ childrenR restR => by
          refine if sameOut : headL = headR then ?_ else none
          subst headR
          refine if sameIn : insL = insR then ?_ else none
          subst insR
          refine if label : kindCode keys kindL = kindCode keys kindR then ?_ else none
          have equal := kind_injective keys kindL kindR label
          subst kindR
          refine if position : mapping.vertices preL.length = preR.length then ?_ else none
          refine if edges : l.addresses.map (Address.rename mapping.vertices) = r.addresses then ?_ else none
          let checked := fun (i : Fin kindL.arity) => scan keys budget (mapping.child preL.length i.val) (childrenL i) (childrenR i)
          refine if complete : ∀ i, (checked i).isSome then ?_ else none
          exact (scan keys budget mapping restL restR).map fun tail =>
            ⟨.bind kindL l r position edges (fun i => ((checked i).get (complete i)).down) tail.down⟩
        | _, _ => none

/-- Check a supplied map. The scan drops every immediately empty γ row,
then compares the remaining rows in order, recursively at each child.
Its internal budget is computed from the size of the decoded tables.
A failed check rejects this map and policy. -/
def check (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] (mapping : Renaming)
    (left : Graph Op args pastL sigsL outs) (right : Graph Op args pastR sigsR outs) :
    Option (PLift (Ordered Op mapping left right)) :=
  (scan keys (termSize left.toTerm + termSize right.toTerm) mapping left.toTerm right.toTerm).map fun cert =>
    ⟨by simpa only [NestedTheta.Graph.toGraph_toTerm] using cert.down⟩

/-- Check actual resolved bodies after comparing the ordered capture
types. The returned certificate is indexed by those precise closures. -/
def checkResolved (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] (mapping : Renaming)
    {fn : Function V S} (left right : Closure Op m.Val fn) : Option (PLift (Resolved m fn left right)) := by
  obtain ⟨contextL, valuesL, sigsL, bodyL⟩ := left
  obtain ⟨contextR, valuesR, sigsR, bodyR⟩ := right
  refine if context : contextL = contextR then ?_ else none
  subst contextR
  exact (check keys mapping bodyL bodyR).map fun cert => ⟨.intro cert.down⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Check.Defs
public import Mathlib.Logic.Equiv.Basic

/-! Infer the candidate renaming from the ordered nonempty rows. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open Local (Renaming)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op}
variable {args outs : Ports (Ty V S)} {sigsL sigsR : List (Ports (Ty V S))}

/-- A pair of active row positions with the child maps in arm order. -/
structure RowPair where
  left : Nat
  right : Nat
  children : List Renaming

abbrev RowPair.separate (a b : RowPair) : Prop := a.left ≠ b.left ∧ a.right ≠ b.right

/-- Close a finite assignment into a natural-number permutation. A swap
installs the current pair and leaves the other assigned targets intact
when the source and target positions are distinct. -/
def completePositions : List RowPair → Nat ≃ Nat
  | [] => Equiv.refl Nat
  | row :: rest =>
    let tail := completePositions rest
    tail.trans (Equiv.swap (tail row.left) row.right)

/-- The skipped empty γ rows carry no output ports, so their positions
need no partners. Swaps give a total extension without matching them.
Child maps are indexed by the original left vertex and arm positions. -/
def completeRows (rows : List RowPair) : Option Renaming :=
  if rows.Pairwise RowPair.separate then
    some (.region (completePositions rows) (fun vertex arm =>
      match rows.find? (fun row => row.left == vertex) with
      | none => .identity
      | some entry => entry.children[arm]?.getD .identity))
  else none

variable [DecidableEq (Ty V S)]

/-- Compare only the table layout here. Typed labels, operands and
results are checked by the supplied-map checker on the original input. -/
def alignRows :
    Nat → {argsL argsR outsL outsR : Ports (Ty V S)} →
    {pastL pastR sigsL sigsR : List (Ports (Ty V S))} →
    Code Op argsL pastL sigsL outsL → Code Op argsR pastR sigsR outsR → Option (List RowPair)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | budget + 1, _, _, _, _, _, _, _, _, left, right =>
    match emptyHead left with
    | some (.intro _ rest) => alignRows budget rest right
    | none =>
      match emptyHead right with
      | some (.intro _ rest) => alignRows budget left rest
      | none =>
        match left, right with
        | .ret _, .ret _ => some []
        | .bind (past := pastL) nodeL childrenL restL, .bind (past := pastR) nodeR childrenR restR =>
          if same : nodeL.kind.arity = nodeR.kind.arity then do
            let children ← (List.ofFn fun (i : Fin nodeL.kind.arity) =>
              (alignRows budget (childrenL i) (childrenR (Fin.cast same i))).bind completeRows).mapM id
            let rest ← alignRows budget restL restR
            pure (⟨pastL.length, pastR.length, children⟩ :: rest)
          else none
        | _, _ => none

/-- Infer a candidate map from the ith non-skipped row on each side and
recurse through the original arm indices. Full region entry starts with
an empty prefix. -/
def inferMap (left : Graph Op args [] sigsL outs) (right : Graph Op args [] sigsR outs) : Option Renaming :=
  (alignRows (termSize left.toTerm + termSize right.toTerm) left.toTerm right.toTerm).bind completeRows

/-- Return the inferred map and the certificate checked on the concrete
numbered region tables. A failure rejects this ordered alignment policy. -/
def infer (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (left : Graph Op args [] sigsL outs) (right : Graph Op args [] sigsR outs) :
    Option ((mapping : Renaming) × PLift (Ordered Op mapping left right)) := do
  let mapping ← inferMap left right
  let certificate ← check keys mapping left right
  pure ⟨mapping, certificate⟩

/-- Infer and check the bodies of the actual resolved callables after
checking their ordered capture types. The family still supplies value
provenance and closure under primitive actions. -/
def inferResolved (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] {fn : Function V S}
    (left right : Closure Op m.Val fn) : Option (PLift (Resolved m fn left right)) := by
  obtain ⟨contextL, valuesL, sigsL, bodyL⟩ := left
  obtain ⟨contextR, valuesR, sigsR, bodyR⟩ := right
  refine if context : contextL = contextR then ?_ else none
  subst contextR
  exact (infer keys bodyL bodyR).map fun pair => ⟨.intro pair.2.down⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs

/-! # Read the cut and reconstitute its two typed components -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize

open TwoBlock.TwoExit (Carrier)
open Wires.Reverse (Vertex isLink readKind readBody)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A I M E D : τ}

structure Components (Φ : Type u) [HasTy Φ τ] (A I M E D : τ) where
  B : τ
  K : τ
  C : τ
  J : τ
  first : Conditional.Guarded Φ A I B K M M
  second : Loop Φ M C J E D

def Components.graph (c : Components Φ A I M E D) : Graph Φ A I M E D :=
  compile c.first c.second

/-- The admitted signature has a unique candidate separator, outer vertex
two. The consumer has one outer θ; all its body uses are in a fresh scope.
Check every input crossing into the separator or the suffix, as well as the
final result wiring, before reading the component labels. -/
def cut (g : Graph Φ A I M E D) :
    Option (List (Vertex (τ := τ) (Φ := Φ)) × List (Vertex (τ := τ) (Φ := Φ))) :=
  match g.toTerm with
  | .bind first firstKids (.bind branch arms (.bind link _ (.bind second secondKids (.ret results)))) =>
    if isLink link.kind &&
        link.inputs.addresses == [.output 1 0, .output 1 1] &&
        second.inputs.addresses == [.output 2 0, .output 2 1] &&
        results.addresses == [.output 3 0, .output 3 1] then do
      let classifier ← readKind first.kind (fun j => readBody (firstKids j))
      let choice ← readKind branch.kind (fun j => readBody (arms j))
      let loop ← readKind second.kind (fun j => readBody (secondKids j))
      pure ([classifier, choice], [loop])
    else none

/-- Bound the recursive parser using the size of the actual nested term.
The bound counts both arm and continuation terms. -/
def budget {Op : Dialect (V := τ) (S := PUnit.{u+1})} :
    {args outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term Op args past sigs outs → Nat
  | _, _, _, _, .ret _ => 1
  | _, _, _, _, .bind node children tail =>
    1 + (List.ofFn (n := node.kind.arity) (fun i => budget (children i))).sum + budget tail

variable [DecidableEq τ]

/-- The component label readers retain typed opcode metadata at every leaf.
The parser chooses right-associated sequencing at each local region. -/
def body : Nat → (A : τ) → List (Vertex (τ := τ) (Φ := Φ)) → Option (Σ B, Body Φ A B)
  | 0, _, _ => none
  | fuel + 1, A, labels =>
    let finish := fun {B : τ} (atom : Body Φ A B) tail =>
      match tail with
      | [] => some ⟨B, atom⟩
      | _ :: _ => do
        let ⟨C, suf⟩ ← body fuel B tail
        pure ⟨C, .sequence atom suf⟩
    match labels with
    | .call (A := a) (B := _b) op :: tail =>
      if aEq : a = A then finish (.instruction (aEq ▸ op)) tail else none
    | .classifier (A := a) (X := l) (Y := r) op :: .gamma [left, right] :: tail =>
      if aEq : a = A then do
        let ⟨b, lbody⟩ ← body fuel l left
        let ⟨c, rbody⟩ ← body fuel r right
        if same : c = b then
          finish (.choice (aEq ▸ op) lbody (same ▸ rbody)) tail
        else none
      else none
    | _ => none

def loop (fuel : Nat) (A E D : τ) :
    List (Vertex (τ := τ) (Φ := Φ)) → Option (Σ B K, Loop Φ A B K E D)
  | [.theta [.header (A := a) (B := b) (E := e) header, .gamma [[.headerExit], bodyAndJoin]]] => do
    match bodyAndJoin.reverse with
    | .join (A := a') (K := k) (D := d) last :: reversed =>
      if ha : a = A then
        if he : e = E then
          if ha' : a' = A then
            if hd : d = D then do
              let ⟨out, inner⟩ ← body fuel b reversed.reverse
              if hk : out = k then
                let h : TwoBlock.Instruction Φ A (Silmaril.coprod E b) := ha ▸ he ▸ header
                let j : TwoBlock.Instruction Φ k (Silmaril.coprod D A) := ha' ▸ hd ▸ last
                pure ⟨b, k, ⟨h, hk ▸ inner, j⟩⟩
              else none
            else none
          else none
        else none
      else none
    | _ => none
  | _ => none

def guarded (fuel : Nat) (A I M : τ) :
    List (Vertex (τ := τ) (Φ := Φ)) → Option (Σ B K, Conditional.Guarded Φ A I B K M M)
  | [.classifier (A := a) (X := x) (Y := y) gate, .gamma [[], loopLabels]] =>
    if ha : a = A then
      if ho : Silmaril.coprod x y = Carrier I M M then do
        let ⟨b, k, inner⟩ ← loop fuel I M M loopLabels
        let op : TwoBlock.Instruction Φ A (Carrier I M M) := ha ▸ ho ▸ gate
        pure ⟨b, k, ⟨op, inner⟩⟩
      else none
    else none
  | _ => none

/-- Decode only the two observed label trees. The candidate is checked
against the original numbered graph by the exact certification step. -/
def candidate (g : Graph Φ A I M E D) : Option (Components Φ A I M E D) := do
  let (producer, consumer) ← cut g
  let fuel := budget g.toTerm
  let ⟨b, k, first⟩ ← guarded fuel A I M producer
  let ⟨c, j, second⟩ ← loop fuel M E D consumer
  pure ⟨b, k, c, j, first, second⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize

module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Thms

/-! # Direct case trees on two-tag atom replies

A binary signature has primitives whose reply is one atom under one of two
tags. It is a tagged signature with two tags of one atom each.

A direct case tree cases on a request itself: `case (op f a) l r`. Each arm
binds the payload atom, and no slot holds the reply. This is the spelling
of the first branching class. The case trees of the tagged signatures bind
the reply first and case on the bound slot: `let₁ (op f a) (case (bv 0) l'
r')`, with the arms under one more slot.

The normal form of a direct case tree is the case tree with the same
requests in the same order, the same exits and the same payloads. Every
slot of the direct tree is renamed past the reply slots that the normal
form binds.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Shape Assembly)
open scoped LetSeq.StraightLine.Structural

/-- Every primitive takes an argument built from atoms, unit and ordered
products, and replies with one atom under the left or the right tag. -/
class BinarySignature (α Φ : Type) where
  argument : Φ → Shape α
  left : Φ → α
  right : Φ → α

namespace Binary

/-- A binary signature as a tagged signature: two tags of one atom each. -/
scoped instance {α Φ : Type} [BinarySignature α Φ] : TaggedSignature α Φ :=
  ⟨BinarySignature.argument, fun f => [BinarySignature.left f], fun f => [[BinarySignature.right f]]⟩

end Binary

open scoped Tagged Binary

variable {α Φ : Type} [BinarySignature α Φ]

/-- A direct case tree over ordered exits. A request node cases on the
request and binds the payload atom in each arm. A leaf returns a payload
assembled from the atom slots in scope, at one exit of its type. -/
inductive DirectTree : {n : Nat} → BoundCtx (Ty α) n → List (Ty α) →
    LetCase.LocallyNameless.Tm Empty Φ n → Type where
  | ret {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {A : Ty α} (exit : ExitAt L A)
      (payload : Assembly β A) : DirectTree β L (exit.term (argTerm payload))
  | ask {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (f : Φ) (argument : Assembly β (instrSrc f))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (left : DirectTree (β.snoc (.base (BinarySignature.left f))) L l)
      (right : DirectTree (β.snoc (.base (BinarySignature.right f))) L r) :
      DirectTree β L (.case (.op f (argTerm argument)) l r)

variable {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}

/-- The native typing of a direct case tree at the packed sum of its
ordered exits. -/
def DirectTree.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    DirectTree β L t → Derivation Φ Γ₀ β t (packedExitType L)
  | _, _, _, .ret exit payload => exit.typing (argTyping payload)
  | _, _, _, .ask f argument left right => .case (.op (f := f) (argTyping argument)) left.typing right.typing

/-- A direct case tree has at least one exit. -/
theorem DirectTree.exits_ne_nil : {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → DirectTree β L t → L ≠ []
  | _, _, _, .ret exit _ => by cases exit <;> exact List.cons_ne_nil _ _
  | _, _, _, .ask _ _ left _ => left.exits_ne_nil

/-- A direct case tree as a captured LetCase operand. -/
def DirectTree.operand {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : DirectTree β L t) :
    Operand Φ β (packedExitType L) :=
  ⟨t, tree.typing⟩

/-- The checked graph that the readback builds from a direct case tree.
Its exits are the original ordered exits. -/
def DirectTree.graph {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : DirectTree β L t) :
    CheckedTable Φ β L :=
  CheckedTable.ofLetCase tree.exits_ne_nil tree.typing

/-- The operand is natively equal to a direct case tree. -/
def Direct (x : Operand Φ β (packedExitType L)) : Prop :=
  ∃ (t : LetCase.LocallyNameless.Tm Empty Φ n) (_ : DirectTree β L t),
    Equiv false Γ₀ β x.1 t (packedExitType L)

/-- The slots of an arm of a direct tree, in the arm of the normal form:
the payload stays newest and every older slot moves past the reply slot. -/
def armRenaming {m : Nat} {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) (reply payload : Ty α) :
    BoundCtx.Renaming (β.snoc payload) ((γ.snoc reply).snoc payload) :=
  (ρ.comp (BoundCtx.Renaming.succ γ reply)).up payload

/-- The normal form of a direct case tree, along a renaming of its slots.
A leaf keeps its exit and renames its payload. A request keeps its
primitive and renames its argument, binds the reply, cases on the bound
slot and continues with the normal forms of the two arms. -/
def DirectTree.normal : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    DirectTree β L t → {m : Nat} → {γ : BoundCtx (Ty α) m} → BoundCtx.Renaming β γ →
    (u : LetCase.LocallyNameless.Tm Empty Φ m) × CaseTree .body γ L u
  | _, _, _, .ret exit payload, _, _, ρ => ⟨_, .ret exit (payload.rename ρ)⟩
  | _, _, _, .ask f argument left right, _, _, ρ =>
    ⟨_, .ask f (argument.rename ρ)
      (.split [BinarySignature.left f] [BinarySignature.right f] []
        (.atom (BinarySignature.left f) (left.normal (armRenaming ρ _ _)).2)
        (.only [BinarySignature.right f]
          (.atom (BinarySignature.right f) (right.normal (armRenaming ρ _ _)).2)))⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

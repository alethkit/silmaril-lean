module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Thms

/-! # Case trees on tagged atom replies

A tagged signature has primitives whose reply is one atom under one of
two tags. The argument is built from atoms, unit and ordered products.

A case tree asks a primitive with an argument assembled from the atom
slots in scope, and cases on the reply. Each arm binds the payload atom
and continues with a case tree. The older slots stay in scope in both
arms. The exits are an ordered list of atom sorts. A leaf returns one
atom slot at one exit of the same sort. Two exits may have the same sort.

An operand is branching when it is natively equal to a case tree. A
bound context is separable when some environment gives distinct tokens to
its atom slots of each sort.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Silmaril.Isotope.Semantics (BoundEnv)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Shape Slot Assembly Separates)
open scoped LetSeq.StraightLine.Structural

/-- Every primitive takes an argument built from atoms, unit and ordered
products, and replies with one atom under the left or the right tag. -/
class TaggedSignature (α Φ : Type) where
  argument : Φ → Shape α
  left : Φ → α
  right : Φ → α

namespace Tagged

scoped instance {α Φ : Type} [TaggedSignature α Φ] : HasTy Φ (Ty α) :=
  ⟨fun f => (TaggedSignature.argument f).ty,
    fun f => .coprod (.base (TaggedSignature.left f)) (.base (TaggedSignature.right f))⟩

end Tagged

open scoped Tagged

variable {α Φ : Type}

/-- All slots are atoms. These are the older captures. -/
inductive AtomContext : {n : Nat} → BoundCtx (Ty α) n → Prop where
  | nil : AtomContext .nil
  | snoc {n : Nat} {β : BoundCtx (Ty α) n} (older : AtomContext β) (a : α) : AtomContext (β.snoc (.base a))

/-- Some environment gives distinct tokens below a bound to the atom slots
of each sort. -/
def Separable {n : Nat} (β : BoundCtx (Ty α) n) : Prop :=
  ∃ (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) (k : Nat), Separates ρ (Set.Iio k)

variable [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n}

/-- The native typing of a slot. -/
def slotTyping {A : Ty α} (s : Slot β A) : Derivation Φ Γ₀ β (.bv s.1) A :=
  cast (congrArg (Derivation Φ Γ₀ β (.bv s.1)) s.2) .bv

/-- An assembled argument as a LetCase term. -/
def argTerm {A : Ty α} : Assembly β A → LetCase.LocallyNameless.Tm Empty Φ n
  | .atom s => .bv s.1
  | .unit => .unit
  | .pair a b => .pair (argTerm a) (argTerm b)

/-- The native typing of an assembled argument. -/
def argTyping {A : Ty α} : (v : Assembly β A) → Derivation Φ Γ₀ β (argTerm v) A
  | .atom s => slotTyping s
  | .unit => .unit
  | .pair a b => .pair (argTyping a) (argTyping b)

/-- A position in the ordered exits, with the atom sort of that exit. -/
inductive ExitAt : List α → α → Type where
  | here {a : α} {L : List α} : ExitAt (a :: L) a
  | there {a b : α} {L : List α} (later : ExitAt L a) : ExitAt (b :: L) a

/-- The ordered exit types of a list of atom sorts. -/
abbrev exitTypes (L : List α) : List (Ty α) := L.map .base

/-- The number of exits before this one. -/
def ExitAt.index {L : List α} {a : α} : ExitAt L a → Nat
  | .here => 0
  | .there later => later.index + 1

/-- Return a term at this exit of the packed sum of the ordered exits. -/
def ExitAt.term {L : List α} {a : α} :
    ExitAt L a → LetCase.LocallyNameless.Tm Empty Φ n → LetCase.LocallyNameless.Tm Empty Φ n
  | .here, t => .inl t
  | .there later, t => .inr (later.term t)

/-- The native typing of a return at this exit. -/
def ExitAt.typing {a : α} {t : LetCase.LocallyNameless.Tm Empty Φ n} :
    {L : List α} → (e : ExitAt L a) → Derivation Φ Γ₀ β t (.base a) →
      Derivation Φ Γ₀ β (e.term t) (packedExitType (exitTypes L))
  | _, .here, d => .inl d
  | _, .there later, d => .inr (later.typing d)

/-- The value of a token returned at this exit. -/
def ExitAt.value {a : α} : {L : List α} → ExitAt L a → Nat →
    LetSeq.StraightLine.Structural.Value (α := α) (packedExitType (exitTypes L))
  | _, .here, x => .inl x
  | _, .there later, x => .inr (later.value x)

/-- A case tree over ordered exits. A request node cases on the tagged
reply and binds the payload atom in each arm. A leaf returns one atom slot
at one exit whose sort is the sort of the slot. -/
inductive CaseTree : {n : Nat} → BoundCtx (Ty α) n → List α → LetCase.LocallyNameless.Tm Empty Φ n → Type where
  | ret {n : Nat} {β : BoundCtx (Ty α) n} {L : List α} {a : α} (exit : ExitAt L a) (s : Slot β (.base a)) :
      CaseTree β L (exit.term (.bv s.1))
  | ask {n : Nat} {β : BoundCtx (Ty α) n} {L : List α} (f : Φ) (argument : Assembly β (instrSrc f))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (left : CaseTree (β.snoc (.base (TaggedSignature.left f))) L l)
      (right : CaseTree (β.snoc (.base (TaggedSignature.right f))) L r) :
      CaseTree β L (.case (.op f (argTerm argument)) l r)

variable {L : List α}

/-- The native typing of a case tree at the packed sum of its ordered exits. -/
def CaseTree.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    CaseTree β L t → Derivation Φ Γ₀ β t (packedExitType (exitTypes L))
  | _, _, _, .ret exit s => exit.typing (slotTyping s)
  | _, _, _, .ask f argument left right => .case (.op (f := f) (argTyping argument)) left.typing right.typing

/-- A case tree has at least one exit. -/
theorem CaseTree.exits_ne_nil : {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → CaseTree β L t → exitTypes L ≠ []
  | _, _, _, .ret exit _ => by cases exit <;> exact List.cons_ne_nil _ _
  | _, _, _, .ask _ _ left _ => left.exits_ne_nil

/-- A case tree as a captured LetCase operand. -/
def CaseTree.operand {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree β L t) :
    Operand Φ β (packedExitType (exitTypes L)) :=
  ⟨t, tree.typing⟩

/-- The operand is natively equal to a case tree. -/
def Branching (x : Operand Φ β (packedExitType (exitTypes L))) : Prop :=
  ∃ (t : LetCase.LocallyNameless.Tm Empty Φ n) (_ : CaseTree β L t),
    Equiv false Γ₀ β x.1 t (packedExitType (exitTypes L))

/-- The checked graph that the readback builds from a case tree. Its
exits are the original ordered exits. -/
def CaseTree.graph {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree β L t) :
    CheckedTable Φ β (exitTypes L) :=
  CheckedTable.ofLetCase tree.exits_ne_nil tree.typing

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

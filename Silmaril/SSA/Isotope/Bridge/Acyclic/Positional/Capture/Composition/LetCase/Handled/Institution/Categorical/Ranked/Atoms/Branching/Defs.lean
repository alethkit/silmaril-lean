module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Thms

/-! # Case trees on tagged atom replies

A tagged signature has primitives whose reply is one atom under one of
two tags. The argument is built from atoms, unit and ordered products.

A case tree asks a primitive with an argument assembled from the atom
slots in scope, and cases on the reply. Each arm binds the payload atom
and continues with a case tree. The older slots stay in scope in both
arms. The exits are an ordered list of types. A leaf returns a payload
at one exit of the type of the payload. The payload is assembled from the
atom slots in scope: an atom slot, the unit, or an ordered pair of
payloads. Two exits may have the same type.

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

/-- A position in the ordered exits, with the type of that exit. -/
inductive ExitAt : List (Ty α) → Ty α → Type where
  | here {A : Ty α} {L : List (Ty α)} : ExitAt (A :: L) A
  | there {A B : Ty α} {L : List (Ty α)} (later : ExitAt L A) : ExitAt (B :: L) A

/-- The number of exits before this one. -/
def ExitAt.index {L : List (Ty α)} {A : Ty α} : ExitAt L A → Nat
  | .here => 0
  | .there later => later.index + 1

/-- Return a term at this exit of the packed sum of the ordered exits. -/
def ExitAt.term {L : List (Ty α)} {A : Ty α} :
    ExitAt L A → LetCase.LocallyNameless.Tm Empty Φ n → LetCase.LocallyNameless.Tm Empty Φ n
  | .here, t => .inl t
  | .there later, t => .inr (later.term t)

/-- The native typing of a return at this exit. -/
def ExitAt.typing {A : Ty α} {t : LetCase.LocallyNameless.Tm Empty Φ n} :
    {L : List (Ty α)} → (e : ExitAt L A) → Derivation Φ Γ₀ β t A →
      Derivation Φ Γ₀ β (e.term t) (packedExitType L)
  | _, .here, d => .inl d
  | _, .there later, d => .inr (later.typing d)

/-- The value of a payload returned at this exit. -/
def ExitAt.value {A : Ty α} : {L : List (Ty α)} → ExitAt L A →
    LetSeq.StraightLine.Structural.Value (α := α) A →
    LetSeq.StraightLine.Structural.Value (α := α) (packedExitType L)
  | _, .here, x => .inl x
  | _, .there later, x => .inr (later.value x)

/-- A case tree over ordered exits. A request node cases on the tagged
reply and binds the payload atom in each arm. A leaf returns a payload
assembled from the atom slots in scope, at one exit of the type of the
payload. The payload is an atom slot, the unit, or an ordered pair of
payloads. -/
inductive CaseTree : {n : Nat} → BoundCtx (Ty α) n → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ n → Type where
  | ret {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {A : Ty α} (exit : ExitAt L A)
      (payload : Assembly β A) : CaseTree β L (exit.term (argTerm payload))
  | ask {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (f : Φ) (argument : Assembly β (instrSrc f))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (left : CaseTree (β.snoc (.base (TaggedSignature.left f))) L l)
      (right : CaseTree (β.snoc (.base (TaggedSignature.right f))) L r) :
      CaseTree β L (.case (.op f (argTerm argument)) l r)

variable {L : List (Ty α)}

/-- The native typing of a case tree at the packed sum of its ordered exits. -/
def CaseTree.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    CaseTree β L t → Derivation Φ Γ₀ β t (packedExitType L)
  | _, _, _, .ret exit payload => exit.typing (argTyping payload)
  | _, _, _, .ask f argument left right => .case (.op (f := f) (argTyping argument)) left.typing right.typing

/-- A case tree has at least one exit. -/
theorem CaseTree.exits_ne_nil : {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → CaseTree β L t → L ≠ []
  | _, _, _, .ret exit _ => by cases exit <;> exact List.cons_ne_nil _ _
  | _, _, _, .ask _ _ left _ => left.exits_ne_nil

/-- A case tree as a captured LetCase operand. -/
def CaseTree.operand {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree β L t) :
    Operand Φ β (packedExitType L) :=
  ⟨t, tree.typing⟩

/-- The operand is natively equal to a case tree. -/
def Branching (x : Operand Φ β (packedExitType L)) : Prop :=
  ∃ (t : LetCase.LocallyNameless.Tm Empty Φ n) (_ : CaseTree β L t),
    Equiv false Γ₀ β x.1 t (packedExitType L)

/-- The checked graph that the readback builds from a case tree. Its
exits are the original ordered exits. -/
def CaseTree.graph {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree β L t) :
    CheckedTable Φ β L :=
  CheckedTable.ofLetCase tree.exits_ne_nil tree.typing

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Thms

/-! # Case trees on tagged atom replies

A tagged signature has primitives whose reply is one atom under one of
two tags. The argument is built from atoms, unit and ordered products.

A case tree asks a primitive with an argument assembled from the atom
slots in scope, and cases on the reply. Each arm binds the payload atom
and continues with a case tree. The older slots stay in scope in both
arms. A leaf returns one atom slot at the single exit.

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

/-- A case tree returning an atom of one sort. A request node cases on the
tagged reply and binds the payload atom in each arm. -/
inductive CaseTree : {n : Nat} → BoundCtx (Ty α) n → α → LetCase.LocallyNameless.Tm Empty Φ n → Type where
  | ret {n : Nat} {β : BoundCtx (Ty α) n} {a : α} (s : Slot β (.base a)) : CaseTree β a (.inl (.bv s.1))
  | ask {n : Nat} {β : BoundCtx (Ty α) n} {a : α} (f : Φ) (argument : Assembly β (instrSrc f))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (left : CaseTree (β.snoc (.base (TaggedSignature.left f))) a l)
      (right : CaseTree (β.snoc (.base (TaggedSignature.right f))) a r) :
      CaseTree β a (.case (.op f (argTerm argument)) l r)

/-- The native typing of a case tree at the single packed exit. -/
def CaseTree.typing {a : α} : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    CaseTree β a t → Derivation Φ Γ₀ β t (packedExitType [.base a])
  | _, _, _, .ret s => .inl (slotTyping s)
  | _, _, _, .ask f argument left right => .case (.op (f := f) (argTyping argument)) left.typing right.typing

/-- A case tree as a captured LetCase operand. -/
def CaseTree.operand {a : α} {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree β a t) :
    Operand Φ β (packedExitType [.base a]) :=
  ⟨t, tree.typing⟩

/-- The operand is natively equal to a case tree. -/
def Branching {a : α} (x : Operand Φ β (packedExitType [.base a])) : Prop :=
  ∃ (t : LetCase.LocallyNameless.Tm Empty Φ n) (_ : CaseTree β a t), Equiv false Γ₀ β x.1 t (packedExitType [.base a])

/-- The checked graph that the readback builds from a case tree. -/
def CaseTree.graph {a : α} {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree β a t) : CheckedTable Φ β [.base a] :=
  CheckedTable.ofLetCase (List.cons_ne_nil _ _) tree.typing

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

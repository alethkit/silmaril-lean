module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Thms

/-! # Case trees on tagged tuple replies

A tagged signature has primitives whose reply carries one of finitely many
ordered tags. Each tag has its own payload: an ordered tuple of atoms,
which may be empty and may differ from tag to tag. There is at least one
tag. The argument is built from atoms, unit and ordered products.

A case tree asks a primitive with an argument assembled from the atom
slots in scope and binds the reply. It then cases on the reply, tag by tag
in order, and in the arm of each tag unpacks the tuple of that tag into
atom slots, component by component in order. Each arm continues with a
case tree. The older slots stay in scope in every arm. The case chain and
the unpacking are forced by the reply type, so a tree has one shape.

The exits are an ordered list of types. A leaf returns a payload at one
exit of the type of the payload. The payload is assembled from the atom
slots in scope: an atom slot, the unit, or an ordered pair of payloads.
Two exits may have the same type.

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

/-- The type of an ordered tuple of atoms. The empty tuple is the unit and
a tuple of one atom is that atom. -/
def tupleTy {α : Type} : List α → Ty α
  | [] => .unit
  | [a] => .base a
  | a :: b :: rest => .product (.base a) (tupleTy (b :: rest))

/-- The type of a reply with ordered tags, each carrying a tuple of atoms.
One tag is its tuple. -/
def tagsTy {α : Type} : List (List α) → Ty α
  | [] => .empty
  | [as] => tupleTy as
  | as :: bs :: rest => .coprod (tupleTy as) (tagsTy (bs :: rest))

/-- Every primitive takes an argument built from atoms, unit and ordered
products. Its reply carries the first tag or one of the other tags, in
order, and each tag has its own tuple of atoms. -/
class TaggedSignature (α Φ : Type) where
  argument : Φ → Shape α
  first : Φ → List α
  others : Φ → List (List α)

/-- The ordered tags of the reply of a primitive. -/
abbrev replyTags {α Φ : Type} [TaggedSignature α Φ] (f : Φ) : List (List α) :=
  TaggedSignature.first f :: TaggedSignature.others f

namespace Tagged

scoped instance {α Φ : Type} [TaggedSignature α Φ] : HasTy Φ (Ty α) :=
  ⟨fun f => (TaggedSignature.argument f).ty, fun f => tagsTy (replyTags f)⟩

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

/-- What a tree must do with the newest slot before anything else. A body
has nothing pending. A pending tuple is unpacked into its atoms. A pending
reply is cased on, tag by tag. -/
inductive Pending (α : Type) where
  | body
  | tuple (atoms : List α)
  | tags (replies : List (List α))

/-- A case tree over ordered exits, in the context of its slots.

A body is a leaf or a request. A leaf returns a payload assembled from the
atom slots in scope, at one exit of the type of the payload. A request
binds the reply and continues with the reply pending at the newest slot.

A pending reply with one tag is its tuple. With more tags it is cased on:
the left arm has the tuple of the first tag pending and the right arm has
the remaining tags pending.

A pending tuple is unpacked in order. The empty tuple and a tuple of one
atom are already slots. A longer tuple is split into its first atom and
the rest, and the rest is pending. -/
inductive CaseTree : Pending α → {n : Nat} → BoundCtx (Ty α) n → List (Ty α) →
    LetCase.LocallyNameless.Tm Empty Φ n → Type where
  | ret {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {A : Ty α} (exit : ExitAt L A)
      (payload : Assembly β A) : CaseTree .body β L (exit.term (argTerm payload))
  | ask {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (f : Φ) (argument : Assembly β (instrSrc f))
      {k : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (reply : CaseTree (.tags (replyTags f)) (β.snoc (tagsTy (replyTags f))) L k) :
      CaseTree .body β L (.let₁ (.op f (argTerm argument)) k)
  | only {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms : List α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (payload : CaseTree (.tuple atoms) (β.snoc (tupleTy atoms)) L t) :
      CaseTree (.tags [atoms]) (β.snoc (tagsTy [atoms])) L t
  | split {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms next : List α) (rest : List (List α))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1)}
      (left : CaseTree (.tuple atoms) ((β.snoc (tagsTy (atoms :: next :: rest))).snoc (tupleTy atoms)) L l)
      (right : CaseTree (.tags (next :: rest))
        ((β.snoc (tagsTy (atoms :: next :: rest))).snoc (tagsTy (next :: rest))) L r) :
      CaseTree (.tags (atoms :: next :: rest)) (β.snoc (tagsTy (atoms :: next :: rest))) L (.case (.bv 0) l r)
  | unit {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (body : CaseTree .body (β.snoc (tupleTy ([] : List α))) L t) :
      CaseTree (.tuple []) (β.snoc (tupleTy ([] : List α))) L t
  | atom {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (a : α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (body : CaseTree .body (β.snoc (tupleTy [a])) L t) : CaseTree (.tuple [a]) (β.snoc (tupleTy [a])) L t
  | pair {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (a b : α) (rest : List α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1 + 1)}
      (later : CaseTree (.tuple (b :: rest))
        (((β.snoc (tupleTy (a :: b :: rest))).snoc (.base a)).snoc (tupleTy (b :: rest))) L t) :
      CaseTree (.tuple (a :: b :: rest)) (β.snoc (tupleTy (a :: b :: rest))) L (.let₂ (.bv 0) t)

variable {L : List (Ty α)} {pending : Pending α}

/-- The native typing of a case tree at the packed sum of its ordered
exits, in its context. -/
def CaseTree.typing : {pending : Pending α} → {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    CaseTree pending β L t → Derivation Φ Γ₀ β t (packedExitType L)
  | _, _, _, _, .ret exit payload => exit.typing (argTyping payload)
  | _, _, _, _, .ask f argument reply => .let₁ (.op (f := f) (argTyping argument)) reply.typing
  | _, _, _, _, .only _ payload => payload.typing
  | _, _, _, _, .split _ _ _ left right => .case .bv left.typing right.typing
  | _, _, _, _, .unit body => body.typing
  | _, _, _, _, .atom _ body => body.typing
  | _, _, _, _, .pair _ _ _ later => .let₂ .bv later.typing

/-- A case tree has at least one exit. -/
theorem CaseTree.exits_ne_nil : {pending : Pending α} → {n : Nat} → {β : BoundCtx (Ty α) n} →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → CaseTree pending β L t → L ≠ []
  | _, _, _, _, .ret exit _ => by cases exit <;> exact List.cons_ne_nil _ _
  | _, _, _, _, .ask _ _ reply => reply.exits_ne_nil
  | _, _, _, _, .only _ payload => payload.exits_ne_nil
  | _, _, _, _, .split _ _ _ left _ => left.exits_ne_nil
  | _, _, _, _, .unit body => body.exits_ne_nil
  | _, _, _, _, .atom _ body => body.exits_ne_nil
  | _, _, _, _, .pair _ _ _ later => later.exits_ne_nil

/-- A body as a captured LetCase operand. -/
def CaseTree.operand {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree .body β L t) :
    Operand Φ β (packedExitType L) :=
  ⟨t, tree.typing⟩

/-- The operand is natively equal to a case tree. -/
def Branching (x : Operand Φ β (packedExitType L)) : Prop :=
  ∃ (t : LetCase.LocallyNameless.Tm Empty Φ n) (_ : CaseTree .body β L t),
    Equiv false Γ₀ β x.1 t (packedExitType L)

/-- The checked graph that the readback builds from a case tree. Its
exits are the original ordered exits. -/
def CaseTree.graph {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree .body β L t) :
    CheckedTable Φ β L :=
  CheckedTable.ofLetCase tree.exits_ne_nil tree.typing

/-- The fresh value of a tuple of atoms: consecutive tokens from a start. -/
def freshTuple : (atoms : List α) → Nat → LetSeq.StraightLine.Structural.Value (α := α) (tupleTy atoms)
  | [], _ => PUnit.unit
  | [_], k => k
  | _ :: b :: rest, k => (k, freshTuple (b :: rest) (k + 1))

/-- A reply at the first of its tags. -/
def firstReply : (atoms : List α) → (rest : List (List α)) →
    LetSeq.StraightLine.Structural.Value (α := α) (tagsTy (atoms :: rest))
  | atoms, [] => freshTuple atoms 0
  | atoms, _ :: _ => .inl (freshTuple atoms 0)

/-- The environments at which the token induction compares two trees.

For a body: one environment that separates the atom slots below a bound.
For a pending tuple: such an environment under the fresh tuple at that
bound. For a pending reply: every reply value, each over an environment
that separates the atom slots below the bound. The environment under a
reply may depend on the reply, because the slots of earlier case splits
hold what was split. -/
def TokenWitness : Pending α → {n : Nat} → (β : BoundCtx (Ty α) n) → Nat →
    (BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β → Prop) → Prop
  | .body, _, _, k, P => ∃ ρ, Separates ρ (Set.Iio k) ∧ P ρ
  | .tuple atoms, _, .snoc β X, k, P =>
    ∃ (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β)
      (x : LetSeq.StraightLine.Structural.Value (α := α) X),
      Separates ρ (Set.Iio k) ∧ HEq x (freshTuple atoms k) ∧ P (ρ.snoc x)
  | .tags _, _, .snoc β X, k, P =>
    ∃ R : LetSeq.StraightLine.Structural.Value (α := α) X →
        BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β,
      (∀ w, Separates (R w) (Set.Iio k)) ∧ ∀ w, P ((R w).snoc w)
  | .tuple _, _, .nil, _, _ => False
  | .tags _, _, .nil, _, _ => False

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

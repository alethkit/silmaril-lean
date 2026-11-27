module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Thms

/-! # Spellings of a request on a tagged tuple reply

The case trees of the tagged signatures bind the reply of a request and
then consume the bound slot. A spelled tree may consume the reply at the
request itself. It has three spellings of the head of a request:

- `let₁ (op f a) k`: bind the reply, as the case trees do;
- `let₂ (op f a) t`: destructure the reply as a pair, when it has one tag
  whose tuple has two or more atoms;
- `case (op f a) l r`: case on the reply, when it has two or more tags.

After the head, the rest of the reply is in a bound slot and is consumed as
in the case trees: remaining tags are cased on in order and tuples are
unpacked in order. Bodies may contain further requests in any of the three
spellings. Leaves are those of the case trees.

The normal form of a spelled tree is the case tree with the same requests
in the same order, the same exits and the same payloads. Every slot of the
spelled tree is renamed past the reply slots that the normal form binds.

A direct case tree is the spelled tree of a binary signature in which
every request is cased on directly. A binary signature has two tags of
one atom each.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Derivation Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Shape Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

/-- The slots under one new slot, past a reply slot bound beneath it: the
new slot stays newest and every older slot moves past the reply slot. -/
def armRenaming {α : Type} {n m : Nat} {β : BoundCtx (Ty α) n} {γ : BoundCtx (Ty α) m}
    (ρ : BoundCtx.Renaming β γ) (reply payload : Ty α) :
    BoundCtx.Renaming (β.snoc payload) ((γ.snoc reply).snoc payload) :=
  (ρ.comp (BoundCtx.Renaming.succ γ reply)).up payload

/-! ## Spelled trees -/

section Spelled

variable {α Φ : Type} [TaggedSignature α Φ]

mutual

/-- A spelled tree in body position: a leaf, or a request followed by one
of the head spellings. -/
inductive Spelled : {n : Nat} → BoundCtx (Ty α) n → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ n → Type where
  | ret {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {A : Ty α} (exit : ExitAt L A)
      (payload : Assembly β A) : Spelled β L (exit.term (argTerm payload))
  | ask {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (f : Φ) (argument : Assembly β (instrSrc f))
      {t : LetCase.LocallyNameless.Tm Empty Φ n}
      (head : SpelledHead (replyTags f) (.op f (argTerm argument)) β L t) : Spelled β L t

/-- The head of a request, consuming the request term itself. It binds the
reply; or destructures a one-tag reply of two or more atoms as a pair; or
cases on a reply of two or more tags. -/
inductive SpelledHead : {n : Nat} → List (List α) → LetCase.LocallyNameless.Tm Empty Φ n →
    BoundCtx (Ty α) n → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ n → Type where
  | bind {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {tags : List (List α)}
      {e : LetCase.LocallyNameless.Tm Empty Φ n} {k : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (reply : SpelledTags tags β L k) : SpelledHead tags e β L (.let₁ e k)
  | destruct {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (a b : α) (rest : List α)
      {e : LetCase.LocallyNameless.Tm Empty Φ n} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1)}
      (later : SpelledTuple (b :: rest) (β.snoc (.base a)) L t) :
      SpelledHead [a :: b :: rest] e β L (.let₂ e t)
  | branch {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms next : List α) (rest : List (List α))
      {e : LetCase.LocallyNameless.Tm Empty Φ n} {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (left : SpelledTuple atoms β L l) (right : SpelledTags (next :: rest) β L r) :
      SpelledHead (atoms :: next :: rest) e β L (.case e l r)

/-- A reply pending at the newest slot, over the base context. One tag is
its tuple; more tags are cased on in order. -/
inductive SpelledTags : {n : Nat} → List (List α) → BoundCtx (Ty α) n → List (Ty α) →
    LetCase.LocallyNameless.Tm Empty Φ (n + 1) → Type where
  | only {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms : List α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (payload : SpelledTuple atoms β L t) : SpelledTags [atoms] β L t
  | split {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms next : List α) (rest : List (List α))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1)}
      (left : SpelledTuple atoms (β.snoc (tagsTy (atoms :: next :: rest))) L l)
      (right : SpelledTags (next :: rest) (β.snoc (tagsTy (atoms :: next :: rest))) L r) :
      SpelledTags (atoms :: next :: rest) β L (.case (.bv 0) l r)

/-- A tuple pending at the newest slot, over the base context. It is
unpacked in order and continues with a body. -/
inductive SpelledTuple : {n : Nat} → List α → BoundCtx (Ty α) n → List (Ty α) →
    LetCase.LocallyNameless.Tm Empty Φ (n + 1) → Type where
  | unit {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (body : Spelled (β.snoc (tupleTy ([] : List α))) L t) : SpelledTuple [] β L t
  | atom {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (a : α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (body : Spelled (β.snoc (tupleTy [a])) L t) : SpelledTuple [a] β L t
  | pair {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (a b : α) (rest : List α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1 + 1)}
      (later : SpelledTuple (b :: rest) ((β.snoc (tupleTy (a :: b :: rest))).snoc (.base a)) L t) :
      SpelledTuple (a :: b :: rest) β L (.let₂ (.bv 0) t)

end

variable {L : List (Ty α)} {n : Nat} {β : BoundCtx (Ty α) n}

mutual

/-- The native typing of a spelled tree at the packed sum of its ordered
exits. -/
def Spelled.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    Spelled β L t → Derivation Φ Γ₀ β t (packedExitType L)
  | _, _, _, .ret exit payload => exit.typing (argTyping payload)
  | _, _, _, .ask f argument head => head.typing (.op (f := f) (argTyping argument))

/-- The native typing of a head, from the typing of the request it
consumes. -/
def SpelledHead.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → SpelledHead tags e β L t →
    Derivation Φ Γ₀ β e (tagsTy tags) → Derivation Φ Γ₀ β t (packedExitType L)
  | _, _, _, _, _, .bind reply, d => .let₁ d reply.typing
  | _, _, _, _, _, .destruct _ _ _ later, d => .let₂ d later.typing
  | _, _, _, _, _, .branch _ _ _ left right, d => .case d left.typing right.typing

/-- The native typing of a pending reply, under its slot. -/
def SpelledTags.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → SpelledTags tags β L t →
    Derivation Φ Γ₀ (β.snoc (tagsTy tags)) t (packedExitType L)
  | _, _, _, _, .only _ payload => payload.typing
  | _, _, _, _, .split _ _ _ left right => .case .bv left.typing right.typing

/-- The native typing of a pending tuple, under its slot. -/
def SpelledTuple.typing : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → SpelledTuple atoms β L t →
    Derivation Φ Γ₀ (β.snoc (tupleTy atoms)) t (packedExitType L)
  | _, _, _, _, .unit body => body.typing
  | _, _, _, _, .atom _ body => body.typing
  | _, _, _, _, .pair _ _ _ later => .let₂ .bv later.typing

end

mutual

/-- The normal form of a spelled tree, along a renaming of its slots. A
leaf keeps its exit and renames its payload. A request keeps its primitive
and renames its argument, binds the reply, and continues with the normal
form of its head. -/
def Spelled.normal : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    Spelled β L t → {m : Nat} → {γ : BoundCtx (Ty α) m} → BoundCtx.Renaming β γ →
    (u : LetCase.LocallyNameless.Tm Empty Φ m) × CaseTree .body γ L u
  | _, _, _, .ret exit payload, _, _, ρ => ⟨_, .ret exit (payload.rename ρ)⟩
  | _, _, _, .ask f argument head, _, _, ρ => ⟨_, .ask f (argument.rename ρ) (head.normal ρ).2⟩

/-- The normal form of a head: the case tree that consumes the bound
reply. A bound head is already of that form. A pair head becomes the
unpacking of the bound pair, and a case head the case on the bound reply,
with every older slot moved past the reply slot. -/
def SpelledHead.normal : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → SpelledHead tags e β L t →
    {m : Nat} → {γ : BoundCtx (Ty α) m} → BoundCtx.Renaming β γ →
    (k : LetCase.LocallyNameless.Tm Empty Φ (m + 1)) × CaseTree (.tags tags) (γ.snoc (tagsTy tags)) L k
  | _, _, _, _, _, .bind reply, _, _, ρ => reply.normal ρ
  | _, _, _, _, _, .destruct a b rest later, _, _, ρ =>
    ⟨_, .only (a :: b :: rest) (.pair a b rest (later.normal (armRenaming ρ _ _)).2)⟩
  | _, _, _, _, _, .branch atoms next rest left right, _, γ, ρ =>
    ⟨_, .split atoms next rest
      (left.normal (ρ.comp (BoundCtx.Renaming.succ γ _))).2
      (right.normal (ρ.comp (BoundCtx.Renaming.succ γ _))).2⟩

/-- The normal form of a pending reply. The renaming is of the base
context and the pending slot stays newest. -/
def SpelledTags.normal : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → SpelledTags tags β L t →
    {m : Nat} → {γ : BoundCtx (Ty α) m} → BoundCtx.Renaming β γ →
    (u : LetCase.LocallyNameless.Tm Empty Φ (m + 1)) × CaseTree (.tags tags) (γ.snoc (tagsTy tags)) L u
  | _, _, _, _, .only atoms payload, _, _, ρ => ⟨_, .only atoms (payload.normal ρ).2⟩
  | _, _, _, _, .split atoms next rest left right, _, _, ρ =>
    ⟨_, .split atoms next rest (left.normal (ρ.up _)).2 (right.normal (ρ.up _)).2⟩

/-- The normal form of a pending tuple. The renaming is of the base
context and the pending slot stays newest. -/
def SpelledTuple.normal : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → SpelledTuple atoms β L t →
    {m : Nat} → {γ : BoundCtx (Ty α) m} → BoundCtx.Renaming β γ →
    (u : LetCase.LocallyNameless.Tm Empty Φ (m + 1)) × CaseTree (.tuple atoms) (γ.snoc (tupleTy atoms)) L u
  | _, _, _, _, .unit body, _, _, ρ => ⟨_, .unit (body.normal (ρ.up _)).2⟩
  | _, _, _, _, .atom a body, _, _, ρ => ⟨_, .atom a (body.normal (ρ.up _)).2⟩
  | _, _, _, _, .pair a b rest later, _, _, ρ =>
    ⟨_, .pair a b rest (later.normal ((ρ.up _).up _)).2⟩

end

/-- A spelled tree has at least one exit. -/
theorem Spelled.exits_ne_nil {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : Spelled β L t) : L ≠ [] :=
  (tree.normal (.id β)).2.exits_ne_nil

/-- A spelled tree as a captured LetCase operand. -/
def Spelled.operand {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : Spelled β L t) :
    Operand Φ β (packedExitType L) :=
  ⟨t, tree.typing⟩

/-- The checked graph that the readback builds from a spelled tree. Its
exits are the original ordered exits. -/
def Spelled.graph {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : Spelled β L t) : CheckedTable Φ β L :=
  CheckedTable.ofLetCase tree.exits_ne_nil tree.typing

/-- The operand is natively equal to a spelled tree. -/
def SpelledOperand (x : Operand Φ β (packedExitType L)) : Prop :=
  ∃ (t : LetCase.LocallyNameless.Tm Empty Φ n) (_ : Spelled β L t),
    Equiv false Γ₀ β x.1 t (packedExitType L)

end Spelled

/-! ## Direct case trees of the binary signatures -/


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

open scoped Binary

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

/-- A direct case tree as a spelled tree: every request is cased on
directly, and each arm has its one atom. -/
def DirectTree.spelled : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    DirectTree β L t → Spelled β L t
  | _, _, _, .ret exit payload => .ret exit payload
  | _, _, _, .ask f argument left right =>
    .ask f argument
      (.branch [BinarySignature.left f] [BinarySignature.right f] []
        (.atom (BinarySignature.left f) left.spelled)
        (.only [BinarySignature.right f] (.atom (BinarySignature.right f) right.spelled)))

/-- The normal form of a direct case tree, along a renaming of its slots.
It is the normal form of its spelled tree. -/
def DirectTree.normal {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : DirectTree β L t) {m : Nat}
    {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) :
    (u : LetCase.LocallyNameless.Tm Empty Φ m) × CaseTree .body γ L u :=
  tree.spelled.normal ρ

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

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

A pending tuple may instead be held, which starts a chain over a stack of
packed tuples. Each tuple of the stack is one slot of the context, and the
stack has any depth. A chain asks a request and binds its reply, which is
pushed on the stack; destructures the newest tuple of the stack by one
pattern let; selects any packed tuple as the one the next pattern let
opens; drops a newest tuple with at most one atom; or, with the stack
empty, continues with any spelled tree. A reply with several tags is
cased on right after its request, and each arm pushes its payload and
continues its own chain. A packed tuple of two or more atoms is not an
atom slot, so no request uses it or its components before they are
destructured.

The normal form unpacks every tuple right after the request or the case
that binds it, and keeps every request and every case in place.

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
open LetSeq.StraightLine.Structural (Shape Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

/-- The slots under one new slot, past a reply slot bound beneath it: the
new slot stays newest and every older slot moves past the reply slot. -/
def armRenaming {α : Type} {n m : Nat} {β : BoundCtx (Ty α) n} {γ : BoundCtx (Ty α) m}
    (ρ : BoundCtx.Renaming β γ) (reply payload : Ty α) :
    BoundCtx.Renaming (β.snoc payload) ((γ.snoc reply).snoc payload) :=
  (ρ.comp (BoundCtx.Renaming.succ γ reply)).up payload

/-! ## Actions on terms that commute with a pattern let -/

section Frame

variable {α Φ : Type} [HasTy Φ (Ty α)]

/-- An action on terms over a telescope that preserves typing and moves a
pattern let on an older pair slot from its body to its front. -/
structure PairFrame (C : Ty α) {m : Nat} (Ω : BoundCtx (Ty α) m) (tel : List (Ty α))
    (term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k) : Prop where
  /-- The action preserves typing. -/
  typed : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω')
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel)},
    LetCase.LocallyNameless.HasType Φ Γ₀ (extendCtx Ω' tel) u C → LetCase.LocallyNameless.HasType Φ Γ₀ Ω' (term ω u) C
  /-- A pattern let on an older pair slot moves in front of the action. -/
  comm : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω') (j : Fin k) {A B : Ty α},
    Ω'.get j = .product A B → ∀ {body : LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel + 1 + 1)},
    LetCase.LocallyNameless.HasType Φ Γ₀ (((extendCtx Ω' tel).snoc A).snoc B) body C →
    Equiv false Γ₀ Ω' (term ω (.let₂ (.bv ((weakenTele Ω' tel).toFun j)) body))
      (.let₂ (.bv j) (term (ω.comp (pastPair Ω' A B)) (body.rename (pairPastTele Ω' tel A B).toFun))) C

end Frame

/-! ## The equation for binding under a pending tuple -/

section Push

variable {α Φ : Type} [TaggedSignature α Φ] {L : List (Ty α)}

/-- The native account of a way to bind a telescope, by an action on
terms. The term of a bound body is the action on the term of the body, and
the action moves a pattern let on an older pair slot from its body to its
front:

`term ω (let₂ x B) = let₂ x (term ω↑↑ B′)`

where `ω↑↑` is `ω` weakened past the two components and `B′` is `B` with
the two components moved beneath the telescope. -/
structure CaseTree.Wrap.Framed {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)}
    (wrap : CaseTree.Wrap Φ L Ω tel)
    (term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k) : Prop where
  /-- The term of the bound body is the action on the term of the body. -/
  spec : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω')
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel)} (r : CaseTree .body (extendCtx Ω' tel) L u),
    (wrap ω r).1 = term ω u
  /-- A pattern let on an older pair slot moves in front of the binding. -/
  comm : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω') (j : Fin k) {A B : Ty α},
    Ω'.get j = .product A B → ∀ {body : LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel + 1 + 1)},
    LetCase.LocallyNameless.HasType Φ Γ₀ (((extendCtx Ω' tel).snoc A).snoc B) body (packedExitType L) →
    Equiv false Γ₀ Ω' (term ω (.let₂ (.bv ((weakenTele Ω' tel).toFun j)) body))
      (.let₂ (.bv j) (term (ω.comp (pastPair Ω' A B)) (body.rename (pairPastTele Ω' tel A B).toFun)))
      (packedExitType L)

/-- Binding a telescope in front of a pending tuple is natively equal to
binding it under the full unpacking of the tuple. -/
def CaseTree.PushedSpec : (pending : Pending α) → {n : Nat} → (β : BoundCtx (Ty α) n) →
    {t : LetCase.LocallyNameless.Tm Empty Φ n} → CaseTree pending β L t → Prop
  | .body, _, _, _, _ => True
  | .tags _, _, _, _, _ => True
  | .tuple _, _, .nil, _, _ => True
  | .tuple _, _, .snoc Ξ T, t, tree =>
    ∀ {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)} (π : BoundCtx.Renaming Ξ (extendCtx Ω tel))
      (wrap : CaseTree.Wrap Φ L Ω tel)
      (term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
        LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k),
      wrap.Framed term →
      Equiv false Γ₀ (Ω.snoc T)
        (term (BoundCtx.Renaming.succ Ω T) (t.rename ((π.up T).comp (swapTele Ω tel T)).toFun))
        (CaseTree.pushed tree π wrap).1 (packedExitType L)

/-- The native typing of the pattern lets that unpack a tuple slot. -/
def unpackTyping : (atoms : List α) → {k : Nat} → {Γ : BoundCtx (Ty α) k} → (s : Slot Γ (tupleTy atoms)) →
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms))} → {C : Ty α} →
    Derivation Φ Γ₀ (extendCtx Γ (pairsTele atoms)) u C → Derivation Φ Γ₀ Γ (unpackAt atoms s.1 u) C
  | [], _, _, _, _, _, d => d
  | [_], _, _, _, _, _, d => d
  | _ :: d :: more, _, _, s, _, _, h => .let₂ (slotTyping s) (unpackTyping (d :: more) ⟨0, rfl⟩ h)

end Push

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
unpacked in order and continues with a body. A tuple of two or more atoms
may instead be held across a chain of requests. -/
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
  | hold {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)} (atoms : List α)
      {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
      (chain : SpelledStack [atoms] (β.snoc (tupleTy atoms)) (.cons ⟨0, rfl⟩ .nil) L t) :
      SpelledTuple atoms β L t

/-- A chain over a stack of packed tuples. Each tuple of the stack is one
slot of the context. The stack is indexed by the atoms of its tuples,
newest first, and has any depth.

- `ask` asks a request and binds its reply. The argument is assembled from
  the atom slots in scope. A packed tuple of two or more atoms is not an
  atom slot, so no request uses it or its components.
- `step` destructures the newest tuple by one pattern let, into its first
  atom and the rest. The rest is the newest tuple of the stack again.
- `unit` and `atom` drop a newest tuple with no atom or one atom. It needs
  no pattern let, and with one atom its slot is an atom slot.
- `done` continues with any spelled tree when the stack is empty.
- `pick` selects any tuple of the stack and moves it to the top. The term
  is unchanged. The next `step`, `unit` or `atom` acts on the selected
  tuple, and the other tuples stay packed in their order.

The reply of a request is pushed on the stack by `SpelledStackTags`, so
unpacking it at once is `step`s right after the request, and keeping it
packed is asking further requests first. Tuples are opened in any order. -/
inductive SpelledStack : (stack : List (List α)) → {m : Nat} → (Δ : BoundCtx (Ty α) m) → Holds Δ stack →
    List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ m → Type where
  | done {m : Nat} {Δ : BoundCtx (Ty α) m} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ m} (body : Spelled Δ L t) :
      SpelledStack [] Δ .nil L t
  | unit {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {top : Slot Δ (tupleTy ([] : List α))}
      {older : Holds Δ stack} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ m} (next : SpelledStack stack Δ older L t) :
      SpelledStack ([] :: stack) Δ (.cons top older) L t
  | atom {c : α} {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {top : Slot Δ (tupleTy [c])}
      {older : Holds Δ stack} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ m} (next : SpelledStack stack Δ older L t) :
      SpelledStack ([c] :: stack) Δ (.cons top older) L t
  | step {a b : α} {rest : List α} {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
      {top : Slot Δ (tupleTy (a :: b :: rest))} {older : Holds Δ stack} {L : List (Ty α)}
      {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
      (next : SpelledStack ((b :: rest) :: stack) ((Δ.snoc (.base a)).snoc (tupleTy (b :: rest)))
        (.cons ⟨0, rfl⟩ (older.rename (pastPair Δ (.base a) (tupleTy (b :: rest))))) L k) :
      SpelledStack ((a :: b :: rest) :: stack) Δ (.cons top older) L (.let₂ (.bv top.1) k)
  | ask {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack} {L : List (Ty α)}
      (g : Φ) (argument : Assembly Δ (instrSrc g)) {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
      (reply : SpelledStackTags stack (replyTags g) Δ holds L k) :
      SpelledStack stack Δ holds L (.let₁ (.op g (argTerm argument)) k)
  | pick {stack : List (List α)} {atoms : List α} {rest : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m}
      {holds : Holds Δ stack} {L : List (Ty α)} {t : LetCase.LocallyNameless.Tm Empty Φ m} (sel : Select stack atoms rest)
      (next : SpelledStack (atoms :: rest) Δ (holds.select sel) L t) : SpelledStack stack Δ holds L t

/-- The bound reply of a request of a chain over a stack, pending at the
newest slot. A reply with one tag is a tuple of atoms and is pushed on the
stack. A reply with more tags is cased on right after its request: the
payload of the first tag is pushed on the stack in its arm, and the other
arms case on the remaining tags. Each arm continues its own chain over the
older tuples, so the chain branches. -/
inductive SpelledStackTags : (stack : List (List α)) → List (List α) → {m : Nat} → (Δ : BoundCtx (Ty α) m) →
    Holds Δ stack → List (Ty α) → LetCase.LocallyNameless.Tm Empty Φ (m + 1) → Type where
  | bind {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {L : List (Ty α)} (atoms : List α) {k : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
      (next : SpelledStack (atoms :: stack) (Δ.snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (holds.rename (BoundCtx.Renaming.succ Δ (tupleTy atoms)))) L k) :
      SpelledStackTags stack [atoms] Δ holds L k
  | split {stack : List (List α)} {m : Nat} {Δ : BoundCtx (Ty α) m} {holds : Holds Δ stack}
      {L : List (Ty α)} (atoms next : List α) (more : List (List α))
      {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)}
      (left : SpelledStack (atoms :: stack)
        ((Δ.snoc (tagsTy (atoms :: next :: more))).snoc (tupleTy atoms))
        (.cons ⟨0, rfl⟩ (holds.rename (pastPair Δ (tagsTy (atoms :: next :: more)) (tupleTy atoms)))) L l)
      (right : SpelledStackTags stack (next :: more) (Δ.snoc (tagsTy (atoms :: next :: more)))
        (holds.rename (BoundCtx.Renaming.succ Δ (tagsTy (atoms :: next :: more)))) L r) :
      SpelledStackTags stack (atoms :: next :: more) Δ holds L (.case (.bv 0) l r)

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
  | _, _, _, _, .hold _ chain => chain.typing

/-- The native typing of a chain over a stack of packed tuples. -/
def SpelledStack.typing : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ m} → SpelledStack stack Δ holds L t →
    Derivation Φ Γ₀ Δ t (packedExitType L)
  | _, _, _, _, _, .done body => body.typing
  | _, _, _, _, _, .unit next => next.typing
  | _, _, _, _, _, .atom next => next.typing
  | _, _, _, .cons top _, _, .step next => .let₂ (slotTyping top) next.typing
  | _, _, _, _, _, .ask g argument reply => .let₁ (.op (f := g) (argTyping argument)) reply.typing
  | _, _, _, _, _, .pick _ next => next.typing

/-- The native typing of the bound reply of a request of such a chain,
under its slot. -/
def SpelledStackTags.typing : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    SpelledStackTags stack tags Δ holds L t → Derivation Φ Γ₀ (Δ.snoc (tagsTy tags)) t (packedExitType L)
  | _, _, _, _, _, _, .bind _ next => next.typing
  | _, _, _, _, _, _, .split _ _ _ left right => .case .bv left.typing right.typing

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
  | _, _, _, _, .hold atoms chain, _, _, ρ =>
    ⟨_, CaseTree.packed atoms (chain.opened (ρ.up (tupleTy atoms))).2⟩

/-- The body of the normal form of a chain over a stack, under the full
unpacking of every tuple of the stack. The slots of the chain are placed
beneath the slots of those unpackings. Each request is asked there, in
order, and the case on a reply directly follows its request. -/
def SpelledStack.opened : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ m} → SpelledStack stack Δ holds L t → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → BoundCtx.Renaming Δ Θ →
    (u : LetCase.LocallyNameless.Tm Empty Φ (stackSize k stack)) × CaseTree .body (stackCtx stack Θ) L u
  | _, _, _, _, _, .done body, _, _, ρ => body.normal ρ
  | _, _, _, _, _, .unit next, _, _, ρ => next.opened ρ
  | _, _, _, _, _, .atom next, _, _, ρ => next.opened ρ
  | (a :: b :: rest) :: stack, _, _, _, _, .step next, _, Θ, ρ =>
    CaseTree.renamed (pending := .body) (next.opened ((ρ.up (.base a)).up (tupleTy (b :: rest)))).2
      (upTele (swapStack stack Θ [.base a, tupleTy (b :: rest)]) (pairsTele (b :: rest)))
  | stack, _, _, _, _, .ask g argument reply, _, Θ, ρ =>
    ⟨_, .ask g (argument.rename (ρ.comp (weakenStack stack Θ))) (reply.opened ρ).2⟩
  | _, _, _, _, _, .pick sel next, _, Θ, ρ =>
    CaseTree.renamed (pending := .body) (next.opened ρ).2 (selectRen sel Θ)

/-- The normal form of the bound reply of a request of such a chain,
pending under the unpackings of the stack. The payload of a tag is
unpacked right after the reply, wherever its chain destructures it. -/
def SpelledStackTags.opened : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    SpelledStackTags stack tags Δ holds L t → {k : Nat} → {Θ : BoundCtx (Ty α) k} →
    BoundCtx.Renaming Δ Θ →
    (u : LetCase.LocallyNameless.Tm Empty Φ (stackSize k stack + 1)) ×
      CaseTree (.tags tags) ((stackCtx stack Θ).snoc (tagsTy tags)) L u
  | stack, _, _, _, _, _, .bind atoms next, _, Θ, ρ =>
    ⟨_, .only atoms (CaseTree.packed atoms
      (CaseTree.renamed (pending := .body) (next.opened (ρ.up (tupleTy atoms))).2
        (upTele (swapStack stack Θ [tupleTy atoms]) (pairsTele atoms))).2)⟩
  | stack, _, _, _, _, _, .split atoms nxt more left right, _, Θ, ρ =>
    ⟨_, .split atoms nxt more
      (CaseTree.packed atoms
        (CaseTree.renamed (pending := .body)
          (left.opened ((ρ.up (tagsTy (atoms :: nxt :: more))).up (tupleTy atoms))).2
          (upTele (swapStack stack Θ [tagsTy (atoms :: nxt :: more), tupleTy atoms]) (pairsTele atoms))).2)
      (CaseTree.renamed (pending := .tags (nxt :: more))
        (β := (stackCtx stack (Θ.snoc (tagsTy (atoms :: nxt :: more)))).snoc (tagsTy (nxt :: more)))
        (right.opened (ρ.up (tagsTy (atoms :: nxt :: more)))).2
        (swapStack stack Θ [tagsTy (atoms :: nxt :: more)])).2⟩

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

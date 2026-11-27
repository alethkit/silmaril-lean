module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.AtomDirect

/-! # Every spelling of a request is natively equal to bind-then-case

The case trees of the tagged signatures bind the reply of a request and
consume the bound slot. A spelled tree may instead consume the reply at
the request: destructure it as a pair, or case on it. The spellings are
related by two native LetCase equations, the existing sequencing laws that
bind the scrutinee of a pattern let and of a case:

`let₂ e c = let₁ e (let₂ (bv 0) c↑)` and `case e l r = let₁ e (case (bv 0) l↑ r↑)`

where `↑` weakens a body past the newly bound slot and keeps its own
binders. Both hold for an effectful scrutinee. They are equations of the
native theory. No model is used.

Applied at every request, under the renaming that moves the slots of the
spelled tree past the reply slots already bound, the laws give a native
equation between a spelled tree and its normal form. The normal form has
the same requests in the same order, the same exits and the same payloads.

So an operand natively equal to a spelled tree is a branching operand, and
the completeness theorem of the tagged signatures applies to every
spelling: a ranked sentence between such entries, at the original ordered
exits, is valid in all supported models exactly when the emitted operands
are natively equal. On the graphs read back from two spelled trees that is
equality of their normal forms. Two different spellings of one tree have
the same normal form, so equality of the trees themselves is not the
criterion.

A pending tuple of two or more atoms may also be held across a chain of
later requests and destructured after them. The spelled term is
`let₁ (op g₁ a₁) (… (let₁ (op gₖ aₖ) (let₂ x t)))` under the tuple slot
`x`. The destructuring binds the first atom and the rest of the tuple, and
the rest is pending again: it is unpacked, or held across a further chain.
The normal form unpacks the whole tuple first. The dependencies are exact.
Each request is assembled from the atom slots in scope. The held tuple is
one slot of product type, not an atom slot, so no request of the chain can
use it or its components. The reply of each request is bound. A reply
with one tag is any tuple of atoms and is unpacked in order,
`let₁ (op g a) (let₂ (bv 0) …)`, and the chain continues under the
unpacking. A reply with several tags is cased on right after its request,
`let₁ (op g a) (case (bv 0) l r)`, and each arm unpacks its tuple and
continues its own chain, ending in its own destructuring of the held
tuple. So a later request may use the atoms of the replies of earlier
ones on its branch, while the held tuple is still one slot, and any
request may use the older atom slots. A request of a further chain may
also use the atoms already unpacked. The body may use every atom of the
tuple, the atoms of the replies of the chains and the older slots.

The spelling and its normal form are related by a derived native
equation, `let₁ E (let₂ x B) = let₂ x (let₁ E↑↑ B′)`, in which the two
components move beneath the binder of the let. It follows from pure-let
beta, pair eta, the law that pulls a pattern let out of the scrutinee of a
let, and pair beta. A second derived equation exchanges two pattern lets on
pair slots, `let₂ x (let₂ y B) = let₂ y (let₂ x B′)`. Together they move a
pattern let on an older pair slot in front of a request whose reply is
bound and unpacked, for a reply of any number of atoms:
`let₁ E (unpack (let₂ x B)) = let₂ x (let₁ E↑↑ (unpack B′))`. The equations
are applied by induction on the chain, on the unpacking of each reply and
on the unpacking of the held tuple; no length is fixed. Each request
occurs once in the normal form, in the same order.

At a reply with several tags the destructuring of the held tuple is in
every arm. A third derived equation moves it out of both arms of a case on
a slot: `case s (let₂ x L) (let₂ x R) = let₂ x (case s L′ R′)`. It follows
from the fact that a term over a pair slot is the destructuring of the slot
around the term at the pair of components, `K[x] = let₂ x (K[(a, b)])`,
from case congruence on the same scrutinee, and from the pattern let on a
pair of slots in each arm. Only the pure destructuring moves. The case
keeps its scrutinee, which is the reply slot, and still directly follows
its request, so no case is moved across a request.

The normal form of a chain is built under the full unpacking of the held
tuple. There the slots of the chain are placed beneath the atoms of the
tuple and the slots of its unpacking, each request is asked in order, and
each reply is unpacked or cased on. The binder permutations are composed
from one renaming that moves a slot bound after a telescope beneath it.
The native equation moves the whole unpacking of the held tuple in front
of each request, of the unpacking of each reply and of each case, by
induction on the held tuple. Normal forms commute with renaming, so the
normal form of a spelled tree in a larger context is the renamed normal
form.

Inside a chain with a held tuple, a fresh reply tuple may be kept packed
as well. The reply of a request with one tag of two or more atoms stays one
slot across a subchain of further requests, each with a one-tag reply that
is unpacked at once, and is then destructured completely; the chain with
the older tuple continues after it. Across the subchain two tuples are
packed. Its requests are assembled from the atom slots in scope, so they
may use older captures and the atoms of earlier replies, and neither packed
tuple. The normal form unpacks the older tuple before the chain and the
fresh tuple right after its own request, and keeps the order of the
requests. The native equation moves each unpacking in front of each request
and each reply unpacking of the subchain by `unpack_out`, with the request
and the reply unpacking as actions that move single pattern lets. Each
unpacking is moved separately, the older one first, so the two holds are
exchanged with every binding of the subchain and no tuple length is fixed.

The covered syntax is exact. A request is followed by one of the three
heads. After a pair head the first atom is a slot and the rest of the
tuple is pending. After a case head each arm has its tuple or the
remaining tags pending. Pending tuples and tags are consumed at once and
in order, as in the case trees, except that a pending tuple of two or more
atoms may be held across a chain of requests as above, and the reply of a
chain request is bound and then unpacked or cased on at once. A one-tag
reply of a chain request may instead be kept packed across a subchain as
above. A chain request whose reply is destructured or cased on at the
request itself, a request with several tags or a further kept tuple inside
such a subchain, an arm payload that is kept packed, destructuring the
older tuple before the fresh one, a case that is not on the reply of the
request before it, holding pending tags, other placements of a
destructuring, and arbitrary LetCase terms are outside it.

A direct case tree is the spelled tree of a binary signature, with two
tags of one atom each, in which every request is cased on directly. For
those trees the normal form determines the tree, and validity on read-back
graphs is equality of the trees.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry denoteRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv HasType)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open scoped LetSeq.StraightLine.Structural Tagged Binary

/-! ## A pair slot commutes with a later binding -/

section Commute

variable {α Φ : Type} [HasTy Φ (Ty α)]

/-- A let followed by a pattern let on an older pair slot is natively
equal to the pattern let followed by the let:

`let₁ E (let₂ x B) = let₂ x (let₁ E↑↑ B′)`

where `x` is a slot of pair type, `E↑↑` is `E` weakened past the two
components, and `B′` is `B` with the two components moved beneath the
binder of the let. `E` may be an effectful request. This is not an axiom
of the native theory. It is derived from native typed laws: pure-let beta
at a slot and at a pair of slots, pair eta at a slot, the sequencing law
that pulls a pattern let out of the scrutinee of a let, and pair beta. -/
theorem let_pair_comm {m : Nat} {Δ : BoundCtx (Ty α) m} {A B X C : Ty α} (j : Fin m)
    (slot : Δ.get j = .product A B) {E : LetCase.LocallyNameless.Tm Empty Φ m}
    {body : LetCase.LocallyNameless.Tm Empty Φ (m + 3)} (hE : HasType Φ Γ₀ Δ E X)
    (hBody : HasType Φ Γ₀ (((Δ.snoc X).snoc A).snoc B) body C) :
    Equiv false Γ₀ Δ (.let₁ E (.let₂ (.bv j.succ) body))
      (.let₂ (.bv j) (.let₁ (E.rename (fun i => i.succ.succ)) (body.rename afterPair))) C :=
  let_pair_comm_proof j slot hE hBody

/-- A pattern let on a pair of slots is natively equal to its body with the
two components renamed to those slots. -/
theorem let_pair_slots {m : Nat} {Γ : BoundCtx (Ty α) m} {A B C : Ty α} (p q : Fin m)
    (hp : Γ.get p = A) (hq : Γ.get q = B) {body : LetCase.LocallyNameless.Tm Empty Φ (m + 2)}
    (hBody : HasType Φ Γ₀ ((Γ.snoc A).snoc B) body C) :
    Equiv false Γ₀ Γ (.let₂ (.pair (.bv p) (.bv q)) body)
      (body.rename (Fin.cases q (Fin.cases p (fun i => i)))) C :=
  let_pair_slots_proof p q hp hq hBody

/-- Two pattern lets on pair slots commute:

`let₂ x (let₂ y B) = let₂ y (let₂ x B′)`

where `x` and `y` are slots of pair type and `B′` is `B` with the two pairs
of components exchanged. Like the equation above this is not an axiom of
the native theory. It is derived from pure-let beta at a slot and at a pair
of slots, pair eta at a slot, the sequencing law that pulls a pattern let
out of the scrutinee of a let, and pair beta. -/
theorem let_pair_pair_comm {m : Nat} {Γ : BoundCtx (Ty α) m} {A B C D E : Ty α} (i j : Fin m)
    (hi : Γ.get i = .product C D) (hj : Γ.get j = .product A B)
    {body : LetCase.LocallyNameless.Tm Empty Φ (m + 4)}
    (hBody : HasType Φ Γ₀ ((((Γ.snoc C).snoc D).snoc A).snoc B) body E) :
    Equiv false Γ₀ Γ (.let₂ (.bv i) (.let₂ (.bv j.succ.succ) body))
      (.let₂ (.bv j) (.let₂ (.bv i.succ.succ) (body.rename afterPairPair))) E :=
  let_pair_pair_comm_proof i j hi hj hBody

/-- A pattern let on an older pair slot, under the pattern lets that
unpack a tuple slot, is natively equal to the pattern let in front of
them. The tuple has any number of atoms. One interchange of pattern lets
is used for each pattern let of the unpacking. -/
theorem unpack_pair_comm (atoms : List α) {k : Nat} {Γ : BoundCtx (Ty α) k} (i j : Fin k)
    (hi : Γ.get i = tupleTy atoms) {A B C : Ty α} (hj : Γ.get j = .product A B)
    {body : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (pairsTele atoms) + 1 + 1)}
    (hBody : HasType Φ Γ₀ (((extendCtx Γ (pairsTele atoms)).snoc A).snoc B) body C) :
    Equiv false Γ₀ Γ
      (unpackAt atoms i (.let₂ (.bv ((weakenTele Γ (pairsTele atoms)).toFun j)) body))
      (.let₂ (.bv j) (unpackAt atoms i.succ.succ
        (body.rename (pairPastTele Γ (pairsTele atoms) A B).toFun))) C :=
  unpack_pair_comm_proof atoms i j hi hj hBody

/-- A bound tuple that is unpacked, followed by a pattern let on an older
pair slot, is natively equal to the pattern let in front of the binding:

`let₁ E (unpack (let₂ x B)) = let₂ x (let₁ E↑↑ (unpack B′))`

where `unpack` is the sequence of pattern lets that unpacks the bound
tuple, `E↑↑` is `E` weakened past the two components, and `B′` is `B` with
the two components moved beneath the tuple slot and the slots of its
unpacking. `E` may be an effectful request. For a tuple of at most one atom
there is no pattern let and this is the equation above. -/
theorem let_unpack_pair_comm (atoms : List α) {k : Nat} {Δ : BoundCtx (Ty α) k} (j : Fin k)
    {A B C : Ty α} (hj : Δ.get j = .product A B) {E : LetCase.LocallyNameless.Tm Empty Φ k}
    (hE : HasType Φ Γ₀ Δ E (tupleTy atoms))
    {body : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (unpackTele atoms) + 1 + 1)}
    (hBody : HasType Φ Γ₀ (((extendCtx Δ (unpackTele atoms)).snoc A).snoc B) body C) :
    Equiv false Γ₀ Δ
      (.let₁ E (unpackAt atoms 0 (.let₂ (.bv ((weakenTele Δ (unpackTele atoms)).toFun j)) body)))
      (.let₂ (.bv j) (.let₁ (E.rename (pastPair Δ A B).toFun)
        (unpackAt atoms 0 (body.rename (pairPastTele Δ (unpackTele atoms) A B).toFun)))) C :=
  let_unpack_pair_comm_proof atoms j hj hE hBody

/-- A term over a pair slot is natively equal to destructuring the slot
and using the pair of components in its place:

`K[x] = let₂ x (K[(a, b)])`

for a slot `x` of pair type. `K` may be any typed term, with requests and
cases. It is derived from pure-let beta at the slot, pair eta, the
sequencing law that pulls a pattern let out of the scrutinee of a let, and
pure-let beta at the pair of components. The equations that move a pattern
let on a pair slot are instances of it. -/
theorem slot_pair_split {m : Nat} {Δ : BoundCtx (Ty α) m} {A B C : Ty α} (j : Fin m)
    (hj : Δ.get j = .product A B) {K : LetCase.LocallyNameless.Tm Empty Φ (m + 1)}
    (hK : HasType Φ Γ₀ (Δ.snoc (.product A B)) K C) :
    Equiv false Γ₀ Δ (LetCase.LocallyNameless.Tm.instantiate K (.bv j))
      (.let₂ (.bv j) (LetCase.LocallyNameless.Tm.instantiate K.underBinder.underBinder (.pair (.bv 1) (.bv 0)))) C :=
  slot_pair_split_proof j hj hK

/-- A case on a slot whose two arms destructure the same older pair slot
is natively equal to destructuring the pair slot first:

`case s (let₂ x L) (let₂ x R) = let₂ x (case s L′ R′)`

where `s` is a slot of sum type, `x` a slot of pair type, and `L′`, `R′`
are the arms with the two components moved beneath the payload of the arm.
The case keeps its scrutinee and its place. Only the pure destructuring
moves, so no case is moved across a request. It follows from the equation
above, case congruence on the same scrutinee, and the pattern let on a pair
of slots in each arm. -/
theorem case_pair_comm {m : Nat} {Δ : BoundCtx (Ty α) m} {A B X Y C : Ty α} (i j : Fin m)
    (hi : Δ.get i = .coprod X Y) (hj : Δ.get j = .product A B)
    {l r : LetCase.LocallyNameless.Tm Empty Φ (m + 3)}
    (hl : HasType Φ Γ₀ (((Δ.snoc X).snoc A).snoc B) l C)
    (hr : HasType Φ Γ₀ (((Δ.snoc Y).snoc A).snoc B) r C) :
    Equiv false Γ₀ Δ (.case (.bv i) (.let₂ (.bv j.succ) l) (.let₂ (.bv j.succ) r))
      (.let₂ (.bv j) (.case (.bv i.succ.succ) (l.rename afterPair) (r.rename afterPair))) C :=
  case_pair_comm_proof i j hi hj hl hr

/-- The whole unpacking of an older tuple slot moves in front of an action
on terms that moves single pattern lets. The tuple has any number of
atoms. -/
theorem unpack_out {C : Ty α} {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)}
    {term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k}
    (frame : PairFrame C Ω tel term) (H : List α) {k : Nat} {Ω' : BoundCtx (Ty α) k}
    (ω : BoundCtx.Renaming Ω Ω') (j : Fin k) (hj : Ω'.get j = tupleTy H)
    {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize (teleSize k tel) (pairsTele H))}
    (hu : HasType Φ Γ₀ (extendCtx (extendCtx Ω' tel) (pairsTele H)) u C) :
    Equiv false Γ₀ Ω' (term ω (unpackAt H ((weakenTele Ω' tel).toFun j) u))
      (unpackAt H j (term (ω.comp (weakenTele Ω' (pairsTele H)))
        (u.rename (swapTeles Ω' tel (pairsTele H)).toFun))) C :=
  unpack_out_proof frame H ω j hj hu

/-- The whole unpacking of an older tuple slot, done in both arms of a
case on a slot, moves in front of the case:

`case s (unpack x L) (unpack x R) = unpack x (case s L′ R′)`

The case keeps its scrutinee. One exchange of the case with a pattern let
is used for each pattern let of the unpacking. -/
theorem case_unpack_out {C : Ty α} (H : List α) {k : Nat} {Γ : BoundCtx (Ty α) k} (i j : Fin k)
    {X Y : Ty α} (hi : Γ.get i = .coprod X Y) (hj : Γ.get j = tupleTy H)
    {l r : LetCase.LocallyNameless.Tm Empty Φ (teleSize (k + 1) (pairsTele H))}
    (hl : HasType Φ Γ₀ (extendCtx (Γ.snoc X) (pairsTele H)) l C)
    (hr : HasType Φ Γ₀ (extendCtx (Γ.snoc Y) (pairsTele H)) r C) :
    Equiv false Γ₀ Γ (.case (.bv i) (unpackAt H j.succ l) (unpackAt H j.succ r))
      (unpackAt H j (.case (.bv ((weakenTele Γ (pairsTele H)).toFun i))
        (l.rename (swapTeles Γ [X] (pairsTele H)).toFun)
        (r.rename (swapTeles Γ [Y] (pairsTele H)).toFun))) C :=
  case_unpack_out_proof H i j hi hj hl hr

/-- Binding by a term is an action on terms that moves a pattern let on an
older pair slot to its front. -/
theorem let_frame {C : Ty α} {m : Nat} {Ω : BoundCtx (Ty α) m} {X : Ty α}
    (E : LetCase.LocallyNameless.Tm Empty Φ m) (hE : HasType Φ Γ₀ Ω E X) :
    PairFrame C Ω [X] (fun ω u => .let₁ (E.rename ω.toFun) u) :=
  let_frame_proof E hE

/-- Unpacking a tuple slot is an action on terms that moves a pattern let
on an older pair slot to its front. -/
theorem unpack_frame {C : Ty α} (atoms : List α) {m : Nat} {Ω : BoundCtx (Ty α) m} (i : Fin m)
    (h : Ω.get i = tupleTy atoms) :
    PairFrame (Φ := Φ) C Ω (pairsTele atoms) (fun ω u => unpackAt atoms (ω.toFun i) u) :=
  unpack_frame_proof atoms i h

end Commute

/-! ## Spelled trees -/

section Spelled

variable {α Φ : Type} [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}
  {t u : LetCase.LocallyNameless.Tm Empty Φ n}

/-- The law at a request that is destructured as a pair: it is natively
equal to binding the reply and destructuring the bound slot, with the body
weakened past that slot. This is the existing sequencing law of the native
theory at an effectful scrutinee. -/
theorem ask_pair_bind (f : Φ) (argument : Assembly β (instrSrc f)) {A B C : Ty α}
    (reply : instrTrg (τ := Ty α) f = .product A B) {c : LetCase.LocallyNameless.Tm Empty Φ (n + 2)}
    (hc : HasType Φ Γ₀ ((β.snoc A).snoc B) c C) :
    Equiv false Γ₀ β (.let₂ (.op f (argTerm argument)) c)
      (.let₁ (.op f (argTerm argument)) (.let₂ (.bv 0) c.underTwoBinders)) C := by
  have typed := (LetCase.LocallyNameless.Derivation.op (f := f) (argTyping argument)).toHasType
  rw [reply] at typed
  exact Equiv.bindPair typed hc

/-- A spelled tree, with its slots renamed, is natively equal to its
normal form along that renaming. -/
theorem spelled_rename_equiv_normal (d : Spelled β L t) {m : Nat} {γ : BoundCtx (Ty α) m}
    (ρ : BoundCtx.Renaming β γ) :
    Equiv false Γ₀ γ (t.rename ρ.toFun) (d.normal ρ).1 (packedExitType L) :=
  d.normal_equiv ρ

/-- A spelled tree is natively equal to its normal form. -/
theorem spelled_equiv_normal (d : Spelled β L t) :
    Equiv false Γ₀ β t (d.normal (.id β)).1 (packedExitType L) := by
  have h := spelled_rename_equiv_normal d (.id β)
  rwa [show (BoundCtx.Renaming.id β).toFun = fun i => i from rfl, LetCase.LocallyNameless.Tm.rename_id] at h

/-- Binding a telescope in front of a pending tuple is natively equal to
binding it under the full unpacking of the tuple. The binding is given by
its native account: its action on terms, and the equation that moves a
pattern let on an older pair slot in front of it. The pending tuple is
given over a context that has the telescope, and its bodies are renamed so
that the telescope is newest. The equation of the account is used once for
each pattern let of the unpacking. -/
theorem CaseTree.pushed_spec {atoms : List α} {T : Ty α} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (tree : CaseTree (.tuple atoms) (β.snoc T) L t) {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)}
    (π : BoundCtx.Renaming β (extendCtx Ω tel)) (wrap : CaseTree.Wrap Φ L Ω tel)
    {term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k}
    (framed : wrap.Framed term) :
    Equiv false Γ₀ (Ω.snoc T)
      (term (BoundCtx.Renaming.succ Ω T) (t.rename ((π.up T).comp (swapTele Ω tel T)).toFun))
      (CaseTree.pushed tree π wrap).1 (packedExitType L) :=
  pushed_spec_proof tree π wrap term framed

/-- The native account of a way to bind a telescope, taken after a
renaming of the base context. -/
theorem CaseTree.Wrap.Framed.after {m k : Nat} {Ω : BoundCtx (Ty α) m} {Ω₁ : BoundCtx (Ty α) k}
    {tel : List (Ty α)} {wrap : CaseTree.Wrap Φ L Ω tel}
    {term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k}
    (framed : wrap.Framed term) (ρ : BoundCtx.Renaming Ω Ω₁) :
    CaseTree.Wrap.Framed (L := L) (Ω := Ω₁) (tel := tel) (fun ω => wrap (ρ.comp ω))
      (fun ω => term (ρ.comp ω)) :=
  framed_after_proof framed ρ

/-- Binding a tuple by `E` and unpacking it has a native account, for a
tuple of any number of atoms: its action on terms is
`let₁ E (unpack ·)`, and a pattern let on an older pair slot moves in front
of it by the equation `let_unpack_pair_comm`. -/
theorem CaseTree.Wrap.unpack_framed (atoms : List α) {m : Nat} {Ω : BoundCtx (Ty α) m}
    (wrap : CaseTree.Wrap Φ L Ω (unpackTele atoms)) (E : LetCase.LocallyNameless.Tm Empty Φ m)
    (hE : HasType Φ Γ₀ Ω E (tupleTy atoms))
    (spec : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k} (ω : BoundCtx.Renaming Ω Ω')
      {u : LetCase.LocallyNameless.Tm Empty Φ (teleSize k (unpackTele atoms))}
      (r : CaseTree .body (extendCtx Ω' (unpackTele atoms)) L u),
      (wrap ω r).1 = .let₁ (E.rename ω.toFun) (unpackAt atoms 0 u)) :
    wrap.Framed (fun ω u => .let₁ (E.rename ω.toFun) (unpackAt atoms 0 u)) :=
  unpack_framed_proof atoms wrap E hE spec

/-- Normal forms commute with renaming: the normal form along a composite
renaming is the normal form along the first renaming, renamed along the
second. -/
theorem spelled_normal_renamed (d : Spelled β L t) {m k : Nat} {γ : BoundCtx (Ty α) m}
    {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) :
    CaseTree.renamed (pending := .body) (d.normal ρ).2 π = d.normal (ρ.comp π) :=
  d.normal_renamed ρ π

/-- The term of the normal form along a composite renaming is the renamed
term of the normal form along the first renaming. -/
theorem spelled_normal_rename_term (d : Spelled β L t) {m k : Nat} {γ : BoundCtx (Ty α) m}
    {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) :
    (d.normal (ρ.comp π)).1 = (d.normal ρ).1.rename π.toFun :=
  (congrArg Sigma.fst (spelled_normal_renamed d ρ π)).symm.trans
    (CaseTree.renamed_body_term (d.normal ρ).2 π)

/-- The same for a pending reply. The renamings are of the context beneath
the pending slot. -/
theorem spelledTags_normal_renamed {tags : List (List α)} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (d : SpelledTags tags β L t) {m k : Nat} {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k}
    (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) :
    CaseTree.renamed (pending := .tags tags) (β := γ.snoc (tagsTy tags)) (d.normal ρ).2 π =
      d.normal (ρ.comp π) :=
  d.normal_renamed ρ π

/-- The same for a pending tuple, unpacked or held. -/
theorem spelledTuple_normal_renamed {atoms : List α} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (d : SpelledTuple atoms β L t) {m k : Nat} {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k}
    (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) :
    CaseTree.renamed (pending := .tuple atoms) (β := γ.snoc (tupleTy atoms)) (d.normal ρ).2 π =
      d.normal (ρ.comp π) :=
  d.normal_renamed ρ π

/-- The term of the normal form of a pending tuple is the unpacking around
the term of its body. -/
theorem spelledTuple_normal_term {atoms : List α} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (d : SpelledTuple atoms β L t) {m : Nat} {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) :
    (d.normal ρ).1 = unpackAt atoms 0 (d.opened ρ).1 :=
  SpelledTuple.normal_term d ρ

/-- The body of the normal form of a chain with a held tuple commutes with
renaming. The body is under the full unpacking of the tuple, and the atoms
of the tuple and the slots of its unpacking stay in place. -/
theorem spelledDelay_opened_renamed {a b : α} {rest : List α} {s : Slot β (tupleTy (a :: b :: rest))}
    (d : SpelledDelay a b rest β s L t) {m k : Nat} {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k}
    (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) :
    CaseTree.renamed (pending := .body) (d.opened ρ).2 (upTele π (pairsTele (a :: b :: rest))) =
      d.opened (ρ.comp π) :=
  d.opened_renamed ρ π

/-- The same for the bound reply of a request of the chain, with one tag
or several. -/
theorem spelledDelayTags_opened_renamed {a b : α} {rest : List α} {tags : List (List α)}
    {s : Slot β (tupleTy (a :: b :: rest))} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (d : SpelledDelayTags a b rest tags β s L t) {m k : Nat} {γ : BoundCtx (Ty α) m}
    {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) :
    CaseTree.renamed (pending := .tags tags)
      (β := (extendCtx γ (pairsTele (a :: b :: rest))).snoc (tagsTy tags))
      (d.opened ρ).2 (upTele π (pairsTele (a :: b :: rest))) = d.opened (ρ.comp π) :=
  d.opened_renamed ρ π

/-- A chain with a held tuple, renamed, is natively equal to unpacking the
whole tuple first and then running the body of its normal form. The chain
may ask requests with one-tag replies of any tuple and requests with
several tags, each followed directly by the case on its reply. -/
theorem spelledDelay_rename_equiv_opened {a b : α} {rest : List α}
    {s : Slot β (tupleTy (a :: b :: rest))} (d : SpelledDelay a b rest β s L t) {m : Nat}
    {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) :
    Equiv false Γ₀ γ (t.rename ρ.toFun)
      (.let₂ (.bv (ρ.toFun s.1)) (unpackAt (b :: rest) 0 (d.opened ρ).1)) (packedExitType L) :=
  (delay_comm d ρ).trans (Equiv.let₂ (.refl (slot_typed (ρ.toFun s.1) ((ρ.typed s.1).trans s.2)))
    (d.opened_flat ρ))

/-- A subchain across which a fresh tuple is kept packed, inside a chain
with an older held tuple, is natively equal to destructuring the older
tuple, unpacking its rest, unpacking the fresh tuple, and then running the
body of the normal form. Both tuples are packed across the subchain. The
older one is destructured first in the normal form, and the fresh one at
the place of its own slot. -/
theorem spelledKept_rename_equiv_opened {a b : α} {rest fresh : List α}
    {s : Slot β (tupleTy (a :: b :: rest))} {x : Slot β (tupleTy fresh)}
    (d : SpelledKept a b rest fresh β s x L t) {m : Nat} {γ : BoundCtx (Ty α) m}
    (ρ : BoundCtx.Renaming β γ) :
    Equiv false Γ₀ γ (t.rename ρ.toFun)
      (.let₂ (.bv (ρ.toFun s.1)) (unpackAt (b :: rest) 0 (unpackAt fresh
        ((weakenTele ((γ.snoc (.base a)).snoc (tupleTy (b :: rest))) (pairsTele (b :: rest))).toFun
          (ρ.toFun x.1).succ.succ) (d.opened ρ).1))) (packedExitType L) :=
  (kept_comm d ρ).trans (Equiv.let₂ (.refl (slot_typed (ρ.toFun s.1) ((ρ.typed s.1).trans s.2)))
    (d.opened_flat ρ))

/-- The body of the normal form of such a subchain commutes with renaming.
The body is under the unpacking of the older tuple and then of the fresh
tuple. -/
theorem spelledKept_opened_renamed {a b : α} {rest fresh : List α}
    {s : Slot β (tupleTy (a :: b :: rest))} {x : Slot β (tupleTy fresh)}
    (d : SpelledKept a b rest fresh β s x L t) {m k : Nat} {γ : BoundCtx (Ty α) m}
    {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) :
    CaseTree.renamed (pending := .body) (d.opened ρ).2
      (upTele (upTele π (pairsTele (a :: b :: rest))) (pairsTele fresh)) = d.opened (ρ.comp π) :=
  d.opened_renamed ρ π

/-- An operand natively equal to a spelled tree is a branching operand: it
is natively equal to the normal form. -/
theorem branching_of_spelled {x : Operand Φ β (packedExitType L)} (spelled : SpelledOperand x) :
    Branching x :=
  let ⟨_, d, same⟩ := spelled
  ⟨_, (d.normal (.id β)).2, same.trans (spelled_equiv_normal d)⟩

/-- A spelled tree is a spelled operand. -/
theorem spelled_operand (d : Spelled β L t) : SpelledOperand d.operand :=
  ⟨t, d, .refl d.typing.toHasType⟩

/-- The graph read back from a spelled tree emits a spelled operand. -/
theorem spelled_graph (d : Spelled β L t) : SpelledOperand d.graph.toLetCase :=
  ⟨t, d, CheckedTable.ofLetCase_emit false d.exits_ne_nil d.typing⟩

/-- Over a separable bound context, two spelled trees are natively equal
exactly when their normal forms are the same term. -/
theorem spelled_equiv_iff_normal (separable : Separable β) (p : Spelled β L t) (q : Spelled β L u) :
    Equiv false Γ₀ β t u (packedExitType L) ↔ (p.normal (.id β)).1 = (q.normal (.id β)).1 :=
  ⟨fun h => (caseTree_equiv_iff separable (p.normal (.id β)).2 (q.normal (.id β)).2).mp
      (((spelled_equiv_normal p).symm.trans h).trans (spelled_equiv_normal q)),
    fun same => (spelled_equiv_normal p).trans
      (((caseTree_equiv_iff separable (p.normal (.id β)).2 (q.normal (.id β)).2).mpr same).trans
        (spelled_equiv_normal q).symm)⟩

/-- A ranked sentence between entries whose emitted operands are natively
equal to spelled trees, over a separable bound context, holds in every
supported model of the ranked room exactly when the emitted operands are
natively equal. The sentence is at the original ordered exits. -/
theorem rankedValid_spelled_iff (separable : Separable β) (l r : RankedEntry Φ β L)
    (hl : SpelledOperand (emitted (P := atomSig α Φ) l)) (hr : SpelledOperand (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      Equiv false Γ₀ β (emitted (P := atomSig α Φ) l).1 (emitted (P := atomSig α Φ) r).1 (packedExitType L) :=
  rankedValid_branching_iff separable l r (branching_of_spelled hl) (branching_of_spelled hr)

/-- Validity of such a sentence is decided by the one ordered trace model
with atoms. -/
theorem rankedValid_spelled_iff_atomTrace (separable : Separable β) (l r : RankedEntry Φ β L)
    (hl : SpelledOperand (emitted (P := atomSig α Φ) l)) (hr : SpelledOperand (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := α) (Φ := Φ)) (atomSig α Φ)).Sat
        (atomTraceRanked α Φ) (sentenceOf l r) :=
  rankedValid_branching_iff_atomTrace separable l r (branching_of_spelled hl) (branching_of_spelled hr)

/-- On the graphs read back from two spelled trees, validity in the ranked
room is equality of their normal forms. -/
theorem rankedValid_spelledTree_iff (separable : Separable β) (p : Spelled β L t) (q : Spelled β L u) :
    RankedValid false (sentenceOf (entryOf p.graph) (entryOf q.graph)) ↔
      (p.normal (.id β)).1 = (q.normal (.id β)).1 :=
  (rankedValid_spelled_iff separable (entryOf p.graph) (entryOf q.graph) (spelled_graph p) (spelled_graph q)).trans
    (Iff.trans
      ⟨fun h => ((CheckedTable.ofLetCase_emit false p.exits_ne_nil p.typing).symm.trans h).trans
          (CheckedTable.ofLetCase_emit false q.exits_ne_nil q.typing),
        fun h => ((CheckedTable.ofLetCase_emit false p.exits_ne_nil p.typing).trans h).trans
          (CheckedTable.ofLetCase_emit false q.exits_ne_nil q.typing).symm⟩
      (spelled_equiv_iff_normal separable p q))

/-- At the ordered trace model with atoms, the original ordered-exit
arrows of the graphs read back from two spelled trees are equal exactly
when their normal forms are the same. -/
theorem denoteRanked_spelledTree_iff (separable : Separable β) (p : Spelled β L t) (q : Spelled β L u) :
    denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf p.graph) =
        denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf q.graph) ↔
      (p.normal (.id β)).1 = (q.normal (.id β)).1 :=
  (rankedValid_spelled_iff_atomTrace separable (entryOf p.graph) (entryOf q.graph) (spelled_graph p)
    (spelled_graph q)).symm.trans (rankedValid_spelledTree_iff separable p q)

/-- The graph read back from a spelled tree and the graph read back from
its normal form are valid together. -/
theorem rankedValid_spelled_normal (separable : Separable β) (d : Spelled β L t) :
    RankedValid false (sentenceOf (entryOf d.graph) (entryOf (d.normal (.id β)).2.graph)) :=
  (rankedValid_branching_iff separable (entryOf d.graph) (entryOf (d.normal (.id β)).2.graph)
    (branching_of_spelled (spelled_graph d)) (branching_graph (d.normal (.id β)).2)).mpr
    (((CheckedTable.ofLetCase_emit false d.exits_ne_nil d.typing).trans (spelled_equiv_normal d)).trans
      (CheckedTable.ofLetCase_emit false (d.normal (.id β)).2.exits_ne_nil (d.normal (.id β)).2.typing).symm)

end Spelled

/-! ## Direct case trees of the binary signatures -/

variable {α Φ : Type} [BinarySignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}
  {t u : LetCase.LocallyNameless.Tm Empty Φ n}

/-! ### The native equation -/

/-- The law at one request: a case on a request is natively equal to
binding the reply and casing on the bound slot, with both arms weakened
past that slot. This is the existing sequencing law of the native theory
at an effectful scrutinee. -/
theorem ask_case_bind (f : Φ) (argument : Assembly β (instrSrc f)) {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    {C : Ty α} (hl : HasType Φ Γ₀ (β.snoc (.base (BinarySignature.left f))) l C)
    (hr : HasType Φ Γ₀ (β.snoc (.base (BinarySignature.right f))) r C) :
    Equiv false Γ₀ β (.case (.op f (argTerm argument)) l r)
      (.let₁ (.op f (argTerm argument)) (.case (.bv 0) l.underBinder r.underBinder)) C :=
  Equiv.bindCase (LetCase.LocallyNameless.Derivation.op (f := f) (argTyping argument)).toHasType hl hr

/-- A direct case tree is a spelled operand, by its spelled tree. -/
theorem spelled_of_direct {x : Operand Φ β (packedExitType L)} (direct : Direct x) : SpelledOperand x :=
  let ⟨t, d, same⟩ := direct
  ⟨t, d.spelled, same⟩

/-- A direct case tree, with its slots renamed, is natively equal to its
normal form along that renaming. -/
theorem direct_rename_equiv_normal (d : DirectTree β L t) {m : Nat} {γ : BoundCtx (Ty α) m}
    (ρ : BoundCtx.Renaming β γ) :
    Equiv false Γ₀ γ (t.rename ρ.toFun) (d.normal ρ).1 (packedExitType L) :=
  normal_equiv_proof d ρ

/-- A direct case tree is natively equal to its normal form. -/
theorem direct_equiv_normal (d : DirectTree β L t) :
    Equiv false Γ₀ β t (d.normal (.id β)).1 (packedExitType L) := by
  have h := direct_rename_equiv_normal d (.id β)
  rwa [show (BoundCtx.Renaming.id β).toFun = fun i => i from rfl, LetCase.LocallyNameless.Tm.rename_id] at h

/-- Two direct case trees with the same normal form are the same term. -/
theorem direct_normal_injective (p : DirectTree β L t) (q : DirectTree β L u)
    (same : (p.normal (.id β)).1 = (q.normal (.id β)).1) : t = u :=
  normal_injective_proof p q (.id β) (fun _ _ h => h) same

/-! ### Coverage -/

/-- An operand natively equal to a direct case tree is a branching
operand: it is natively equal to the normal form. -/
theorem branching_of_direct {x : Operand Φ β (packedExitType L)} (direct : Direct x) : Branching x :=
  let ⟨_, d, same⟩ := direct
  ⟨_, (d.normal (.id β)).2, same.trans (direct_equiv_normal d)⟩

/-- A direct case tree is a direct operand. -/
theorem direct_operand (d : DirectTree β L t) : Direct d.operand :=
  ⟨t, d, .refl d.typing.toHasType⟩

/-- The graph read back from a direct case tree emits a direct operand. -/
theorem direct_graph (d : DirectTree β L t) : Direct d.graph.toLetCase :=
  ⟨t, d, CheckedTable.ofLetCase_emit false d.exits_ne_nil d.typing⟩

/-! ### Completeness for the direct syntax -/

/-- Over a separable bound context, two direct case trees are natively
equal exactly when they are the same term. -/
theorem directTree_equiv_iff (separable : Separable β) (p : DirectTree β L t) (q : DirectTree β L u) :
    Equiv false Γ₀ β t u (packedExitType L) ↔ t = u :=
  ⟨fun h => direct_normal_injective p q
      ((caseTree_equiv_iff separable (p.normal (.id β)).2 (q.normal (.id β)).2).mp
        (((direct_equiv_normal p).symm.trans h).trans (direct_equiv_normal q))),
    fun same => by
      cases same
      exact .refl p.typing.toHasType⟩

/-- A ranked sentence between entries whose emitted operands are natively
equal to direct case trees, over a separable bound context, holds in every
supported model of the ranked room exactly when the emitted operands are
natively equal. The sentence is at the original ordered exits. -/
theorem rankedValid_direct_iff (separable : Separable β) (l r : RankedEntry Φ β L)
    (hl : Direct (emitted (P := atomSig α Φ) l)) (hr : Direct (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      Equiv false Γ₀ β (emitted (P := atomSig α Φ) l).1 (emitted (P := atomSig α Φ) r).1 (packedExitType L) :=
  rankedValid_branching_iff separable l r (branching_of_direct hl) (branching_of_direct hr)

/-- Validity of such a sentence is decided by the one ordered trace model
with atoms. -/
theorem rankedValid_direct_iff_atomTrace (separable : Separable β) (l r : RankedEntry Φ β L)
    (hl : Direct (emitted (P := atomSig α Φ) l)) (hr : Direct (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := α) (Φ := Φ)) (atomSig α Φ)).Sat
        (atomTraceRanked α Φ) (sentenceOf l r) :=
  rankedValid_branching_iff_atomTrace separable l r (branching_of_direct hl) (branching_of_direct hr)

/-- On the graphs read back from two direct case trees, validity in the
ranked room is equality of the two trees. -/
theorem rankedValid_directTree_iff (separable : Separable β) (p : DirectTree β L t) (q : DirectTree β L u) :
    RankedValid false (sentenceOf (entryOf p.graph) (entryOf q.graph)) ↔ t = u :=
  (rankedValid_direct_iff separable (entryOf p.graph) (entryOf q.graph) (direct_graph p) (direct_graph q)).trans
    (Iff.trans
      ⟨fun h => ((CheckedTable.ofLetCase_emit false p.exits_ne_nil p.typing).symm.trans h).trans
          (CheckedTable.ofLetCase_emit false q.exits_ne_nil q.typing),
        fun h => ((CheckedTable.ofLetCase_emit false p.exits_ne_nil p.typing).trans h).trans
          (CheckedTable.ofLetCase_emit false q.exits_ne_nil q.typing).symm⟩
      (directTree_equiv_iff separable p q))

/-- At the ordered trace model with atoms, the original ordered-exit
arrows of the graphs read back from two direct case trees are equal
exactly when the trees are the same. -/
theorem denoteRanked_directTree_iff (separable : Separable β) (p : DirectTree β L t) (q : DirectTree β L u) :
    denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf p.graph) =
        denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf q.graph) ↔ t = u :=
  (rankedValid_direct_iff_atomTrace separable (entryOf p.graph) (entryOf q.graph) (direct_graph p)
    (direct_graph q)).symm.trans (rankedValid_directTree_iff separable p q)

/-- The graph read back from a direct case tree and the graph read back
from its normal form are valid together: the two spellings are one
sentence up to native equality. -/
theorem rankedValid_direct_normal (separable : Separable β) (d : DirectTree β L t) :
    RankedValid false (sentenceOf (entryOf d.graph) (entryOf (d.normal (.id β)).2.graph)) :=
  (rankedValid_branching_iff separable (entryOf d.graph) (entryOf (d.normal (.id β)).2.graph)
    (branching_of_direct (direct_graph d)) (branching_graph (d.normal (.id β)).2)).mpr
    (((CheckedTable.ofLetCase_emit false d.exits_ne_nil d.typing).trans (direct_equiv_normal d)).trans
      (CheckedTable.ofLetCase_emit false (d.normal (.id β)).2.exits_ne_nil (d.normal (.id β)).2.typing).symm)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

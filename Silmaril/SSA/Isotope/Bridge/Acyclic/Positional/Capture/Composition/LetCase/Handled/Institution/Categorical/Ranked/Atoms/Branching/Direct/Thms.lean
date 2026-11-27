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

A pending tuple may also be held across later requests, and several
tuples may be packed at once. A chain runs over a stack of packed tuples,
each one slot of the context. The stack is one index of the grammar and has
any depth; there is no grammar per number of holds. A chain asks a request
and binds its reply; or destructures the newest tuple of the stack by one
pattern let, into its first atom and the rest; or drops a newest tuple with
at most one atom; or, with the stack empty, continues with any spelled
tree. The reply of a request is pushed on the stack. With one tag it is a
tuple. With several tags it is cased on right after its request,
`let₁ (op g a) (case (bv 0) l r)`, each arm pushes the payload of its tag,
and each arm continues its own chain, so the chain branches. Unpacking a
reply or an arm payload at once is destructuring it right away, and keeping
it packed is asking further requests first. Tuples are opened newest first.

The dependencies are exact. Each request is assembled from the atom slots
in scope. A packed tuple of two or more atoms is one slot of product type,
not an atom slot, so no request can use it or its components until they
are destructured. A request may use the older atom slots and the atoms
already destructured on its branch.

The normal form unpacks every tuple completely right after the request or
the case that binds it. It keeps every request, with its argument, and
every case in place: a case is still on the reply of its request and
directly follows it. No case is moved across a request.

The spelling and its normal form are related by derived native equations.
None is an axiom of the native theory. `let₁ E (let₂ x B) = let₂ x (let₁
E↑↑ B′)` moves a pattern let on an older pair slot in front of a binding;
`let₂ x (let₂ y B) = let₂ y (let₂ x B′)` exchanges two pattern lets on pair
slots; and `case s (let₂ x L) (let₂ x R) = let₂ x (case s L′ R′)` moves one
out of both arms of a case on a slot. They follow from pure-let beta, pair
eta, the law that pulls a pattern let out of the scrutinee of a let, pair
beta, and case congruence on the same scrutinee, through
`K[x] = let₂ x (K[(a, b)])` for a term over a pair slot. By induction on a
tuple they move its whole unpacking, and by induction on the stack they
move the unpackings of every packed tuple, in front of any binding that
moves single pattern lets (`stack_out`) and out of both arms of a case
(`case_stack_out`). A request, the unpacking of a tuple and a single
pattern let are such bindings.

The normal form of a chain is built under the unpackings of its stack. The
binder permutations are renamings of a context under a stack, defined by
recursion on the stack from one renaming that moves a slot bound after a
telescope beneath it; no tuple length and no stack depth is fixed. Normal
forms commute with renaming, so the normal form of a spelled tree in a
larger context is the renamed normal form.

The covered syntax is exact. A request is followed by one of the three
heads. After a pair head the first atom is a slot and the rest of the
tuple is pending. After a case head each arm has its tuple or the
remaining tags pending. Pending tuples and tags are consumed at once and
in order, as in the case trees, except that a pending tuple may be held
and starts a chain over a stack as above. Outside it are: opening a packed
tuple that is not the newest; a request whose reply is destructured or
cased on at the request itself while a tuple is packed; a reply with
several tags that is kept as one slot, so that its case does not directly
follow its request; and arbitrary LetCase terms.

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

/-- A pattern let on a pair slot is an action on terms that moves a pattern
let on an older pair slot to its front. -/
theorem pair_frame {C : Ty α} {m : Nat} {Ω : BoundCtx (Ty α) m} {A B : Ty α} (i : Fin m)
    (h : Ω.get i = .product A B) :
    PairFrame (Φ := Φ) C Ω [A, B] (fun ω u => .let₂ (.bv (ω.toFun i)) u) :=
  pair_frame_proof i h

/-- The indexed interchange over a stack. The unpackings of every tuple of
a stack of packed tuples move in front of an action on terms that moves
single pattern lets:

`term (unpack stack u) = unpack stack (term u′)`

where `u′` is `u` with the telescope of the action moved beneath the slots
of the unpackings. The stack has any depth and its tuples any length. -/
theorem stack_out {C : Ty α} {m : Nat} {Ω : BoundCtx (Ty α) m} {tel : List (Ty α)}
    {term : ∀ {k : Nat} {Ω' : BoundCtx (Ty α) k}, BoundCtx.Renaming Ω Ω' →
      LetCase.LocallyNameless.Tm Empty Φ (teleSize k tel) → LetCase.LocallyNameless.Tm Empty Φ k}
    (frame : PairFrame C Ω tel term) (stack : List (List α)) {k : Nat} {Ω' : BoundCtx (Ty α) k}
    (ω : BoundCtx.Renaming Ω Ω') (H : Holds Ω' stack)
    {u : LetCase.LocallyNameless.Tm Empty Φ (stackSize (teleSize k tel) stack)}
    (hu : HasType Φ Γ₀ (stackCtx stack (extendCtx Ω' tel)) u C) :
    Equiv false Γ₀ Ω' (term ω (unpackStack stack (H.rename (weakenTele Ω' tel)) u))
      (unpackStack stack H (term (ω.comp (weakenStack stack Ω'))
        (u.rename (swapStack stack Ω' tel).toFun))) C :=
  stack_out_proof frame stack ω H hu

/-- The unpackings of every tuple of a stack, done in both arms of a case
on a slot, move in front of the case:

`case s (unpack stack L) (unpack stack R) = unpack stack (case s L′ R′)`

The case keeps its scrutinee. -/
theorem case_stack_out {C : Ty α} (stack : List (List α)) {k : Nat} {Γ : BoundCtx (Ty α) k} (i : Fin k)
    {X Y : Ty α} (hi : Γ.get i = .coprod X Y) (H : Holds Γ stack)
    {l r : LetCase.LocallyNameless.Tm Empty Φ (stackSize (k + 1) stack)}
    (hl : HasType Φ Γ₀ (stackCtx stack (Γ.snoc X)) l C) (hr : HasType Φ Γ₀ (stackCtx stack (Γ.snoc Y)) r C) :
    Equiv false Γ₀ Γ
      (.case (.bv i) (unpackStack stack (H.rename (weakenTele Γ [X])) l)
        (unpackStack stack (H.rename (weakenTele Γ [Y])) r))
      (unpackStack stack H (.case (.bv ((weakenStack stack Γ).toFun i))
        (l.rename (swapStack stack Γ [X]).toFun) (r.rename (swapStack stack Γ [Y]).toFun))) C :=
  case_stack_out_proof stack i hi H hl hr

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

/-- A chain over a stack of packed tuples, renamed, is natively equal to
unpacking every tuple of the stack, oldest outermost, and then running the
body of its normal form. The stack has any depth. -/
theorem spelledStack_rename_equiv_opened {stack : List (List α)} {holds : Holds β stack}
    (d : SpelledStack stack β holds L t) {m : Nat} {γ : BoundCtx (Ty α) m} (ρ : BoundCtx.Renaming β γ) :
    Equiv false Γ₀ γ (t.rename ρ.toFun) (unpackStack stack (holds.rename ρ) (d.opened ρ).1)
      (packedExitType L) :=
  d.opened_equiv ρ

/-- The body of the normal form of a chain over a stack commutes with
renaming. The slots of the unpackings of the stack stay in place. -/
theorem spelledStack_opened_renamed {stack : List (List α)} {holds : Holds β stack}
    (d : SpelledStack stack β holds L t) {m k : Nat} {γ : BoundCtx (Ty α) m} {δ : BoundCtx (Ty α) k}
    (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) :
    CaseTree.renamed (pending := .body) (d.opened ρ).2 (upStack stack π) = d.opened (ρ.comp π) :=
  d.opened_renamed ρ π

/-- The same for the bound reply of a request of such a chain, with one tag
or several. -/
theorem spelledStackTags_opened_renamed {stack : List (List α)} {tags : List (List α)}
    {holds : Holds β stack} {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (d : SpelledStackTags stack tags β holds L t) {m k : Nat} {γ : BoundCtx (Ty α) m}
    {δ : BoundCtx (Ty α) k} (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) :
    CaseTree.renamed (pending := .tags tags) (β := (stackCtx stack γ).snoc (tagsTy tags))
      (d.opened ρ).2 (upStack stack π) = d.opened (ρ.comp π) :=
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

module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.AtomBranching

/-! # Completeness for case trees on tagged tuple replies

The ordered trace interpretation whose atoms are natural numbers reflects
native equality of branching operands. This is proved, not assumed.

A reply carries one of finitely many ordered tags, and each tag has its
own ordered tuple of atoms. A request binds the reply, cases on it tag by
tag in order, and unpacks the tuple of the chosen tag into atom slots in
order. The exits are an ordered list of types, and a leaf returns a
payload assembled from the atom slots in scope at one exit of the type of
the payload.

At an environment that gives distinct tokens to the atom slots, two case
trees with the same ordered traces are the same term. The induction
follows the tree.

- A leaf is determined by the value it returns: the value fixes the exit
  position, the exit type and the payload value, and at distinct tokens
  the payload value fixes the payload tree.
- A request is determined by its first logged event, which records the
  primitive and the tokens of the argument. Every reply value is
  possible, so the run of the request contains the run of its
  continuation at every reply.
- A case split on the bound reply runs the arm of the tag of the reply.
  The two arms are compared at the replies of their own tags.
- A tuple is compared at consecutive unused tokens. Unpacking binds its
  first atom at the next token and continues with the rest. Every newly
  bound atom slot gets a token that no older slot has.

Slots that hold a bound reply or a tuple of two or more atoms are not
atom slots. They stay in scope and do not affect the separation.

A ranked sentence between entries whose emitted operands are natively
equal to case trees, over a separable bound context, is therefore valid in
all supported models exactly when the emitted operands are natively equal.
The sentence is at the original ordered exits of the entries. On the
graphs read back from two case trees, validity is equality of the trees,
and so is equality of their ordered-exit arrows at the one model.

The class is exact. A reply has at least one tag and each tag carries a
flat ordered tuple of atoms. Every request is followed at once by the
full case split and unpacking of its reply. Each leaf returns one
assembled payload at one exit of its type. Reply payloads with nested
products or sums, cases on other scrutinees, partial or reordered
unpacking, and returned payloads that contain sums are outside it.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Silmaril.Isotope.Semantics (BoundEnv)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry denoteRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Reply (Γ₀ run traceArrow)
open LetSeq.StraightLine.Structural (Assembly Separates)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}

/-! ## Separating environments -/

/-- A separating environment extends by the next unused token at a new
atom slot. -/
theorem separates_fresh {ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β} {k : Nat}
    (sep : Separates ρ (Set.Iio k)) (a : α) :
    Separates (ρ.snoc (A := Ty.base a) (k : Nat)) (Set.Iio (k + 1)) :=
  separates_fresh_proof sep a

/-- A context of older atom captures is separable. -/
theorem separable_atoms (atoms : AtomContext β) : Separable β :=
  separable_atoms_proof atoms

/-- A separable context stays separable under a new atom slot. -/
theorem separable_snoc (separable : Separable β) (a : α) : Separable (β.snoc (.base a)) :=
  let ⟨ρ, k, sep⟩ := separable
  ⟨ρ.snoc (A := Ty.base a) (k : Nat), k + 1, separates_fresh sep a⟩

omit [TaggedSignature α Φ] in
/-- A separating environment stays separating under a new slot that is
not an atom: a bound reply, a tuple of two or more atoms, or the unit. -/
theorem separates_other {ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β} {used : Set Nat}
    (sep : Separates ρ used) {X : Ty α} (other : ∀ a, X ≠ .base a)
    (x : LetSeq.StraightLine.Structural.Value (α := α) X) : Separates (ρ.snoc x) used :=
  separates_other_proof sep other x

/-! ## The reductions at a request, a case split and a tuple -/

variable {t u : LetCase.LocallyNameless.Tm Empty Φ n}

/-- At a request with the same primitive and argument, the ordered traces
agree exactly when the continuations agree at every reply. The older
slots keep their values. -/
theorem ask_run_eq_iff (f : Φ) (argument : Assembly β (instrSrc f))
    {k k' : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (reply : CaseTree (.tags (replyTags f)) (β.snoc (tagsTy (replyTags f))) L k)
    (reply' : CaseTree (.tags (replyTags f)) (β.snoc (tagsTy (replyTags f))) L k')
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) :
    run (CaseTree.ask f argument reply).typing ρ = run (CaseTree.ask f argument reply').typing ρ ↔
      ∀ w : LetSeq.StraightLine.Structural.Value (α := α) (tagsTy (replyTags f)),
        run reply.typing (ρ.snoc w) = run reply'.typing (ρ.snoc w) :=
  ask_run_eq_iff_proof f argument reply reply' ρ

/-- A case split on a pending reply runs the arm of the tag of the reply:
the left arm with the tuple of the first tag, or the right arm with the
reply at the remaining tags. -/
theorem run_split (atoms next : List α) (rest : List (List α))
    {l r : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1)}
    (left : CaseTree (.tuple atoms) ((β.snoc (tagsTy (atoms :: next :: rest))).snoc (tupleTy atoms)) L l)
    (right : CaseTree (.tags (next :: rest))
      ((β.snoc (tagsTy (atoms :: next :: rest))).snoc (tagsTy (next :: rest))) L r)
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β)
    (w : LetSeq.StraightLine.Structural.Value (α := α) (tagsTy (atoms :: next :: rest))) :
    run (CaseTree.split atoms next rest left right).typing (ρ.snoc w) =
      Sum.elim (fun x => run left.typing ((ρ.snoc w).snoc x)) (fun y => run right.typing ((ρ.snoc w).snoc y)) w :=
  run_split_proof atoms next rest left right ρ w

/-- Unpacking a pending tuple of two or more atoms binds its first atom
and the rest, in that order. -/
theorem run_pair (a b : α) (rest : List α) {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1 + 1 + 1)}
    (later : CaseTree (.tuple (b :: rest))
      (((β.snoc (tupleTy (a :: b :: rest))).snoc (.base a)).snoc (tupleTy (b :: rest))) L t)
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β)
    (w : LetSeq.StraightLine.Structural.Value (α := α) (tupleTy (a :: b :: rest))) :
    run (CaseTree.pair a b rest later).typing (ρ.snoc w) =
      run later.typing (((ρ.snoc w).snoc (A := Ty.base a) w.1).snoc w.2) :=
  run_pair_proof a b rest later ρ w

/-! ## Exits and payloads -/

omit [TaggedSignature α Φ] in
/-- The value returned at an exit fixes the type of the exit, the payload
value and the position of the exit among the ordered exits. Two exits of
the same type with the same payload are told apart. -/
theorem ExitAt.value_inj {A B : Ty α} (e : ExitAt L A) (e' : ExitAt L B)
    (x : LetSeq.StraightLine.Structural.Value (α := α) A) (y : LetSeq.StraightLine.Structural.Value (α := α) B)
    (same : e.value x = e'.value y) : ∃ type : A = B, type ▸ x = y ∧ e.index = e'.index :=
  exit_value_index_proof e e' x y same

omit [TaggedSignature α Φ] in
/-- An assembled payload is determined by its value at an environment that
separates the atom slots. The payload grammar has one tree for each
product of atom slots, so a changed component or a changed order is a
different value. -/
theorem payload_value_injective {A : Ty α} {ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β}
    {used : Set Nat} (sep : Separates ρ used) : Function.Injective (Assembly.value (A := A) ρ) :=
  payload_inj_proof sep

/-- A leaf returns the value of its payload at its exit. -/
theorem run_ret {A : Ty α} (exit : ExitAt L A) (payload : Assembly β A)
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) :
    run (CaseTree.ret (Φ := Φ) exit payload).typing ρ = pure (exit.value (payload.value ρ)) :=
  run_ret_proof exit payload ρ

/-- The leaf reflection. Two leaves with the same ordered traces at an
environment that separates the atom slots return at the same exit
position, at the same exit type, the same payload tree. -/
theorem ret_eq_of_run {A B : Ty α} (e : ExitAt L A) (e' : ExitAt L B) (p : Assembly β A) (q : Assembly β B)
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) {used : Set Nat} (sep : Separates ρ used)
    (same : run (CaseTree.ret (Φ := Φ) e p).typing ρ = run (CaseTree.ret (Φ := Φ) e' q).typing ρ) :
    ∃ type : A = B, type ▸ p = q ∧ e.index = e'.index :=
  ret_eq_of_run_proof e e' p q ρ sep same

/-! ## Separation of case trees -/

/-- The token induction, at any pending state. Two case trees whose runs
agree at the environments of `TokenWitness` are the same term. -/
theorem caseTree_eq_of_witness {pending : Pending α} (p : CaseTree pending β L t) (q : CaseTree pending β L u)
    (k : Nat) (witness : TokenWitness pending β k (fun ρ => run p.typing ρ = run q.typing ρ)) : t = u :=
  caseTree_eq_of_witness_proof p q k witness

/-- Two case trees with the same ordered traces at one environment that
separates the atom slots are the same term. -/
theorem caseTree_eq_of_run (p : CaseTree .body β L t) (q : CaseTree .body β L u)
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) (k : Nat)
    (sep : Separates ρ (Set.Iio k)) (same : run p.typing ρ = run q.typing ρ) : t = u :=
  caseTree_eq_of_run_proof p q ρ k sep same

/-- The ordered trace interpretation with atoms reflects native equality
of branching operands over a separable bound context. -/
theorem branching_reflects (separable : Separable β) (x y : Operand Φ β (packedExitType L))
    (hx : Branching x) (hy : Branching y) (same : traceArrow x.2 = traceArrow y.2) :
    Equiv false Γ₀ β x.1 y.1 (packedExitType L) :=
  branching_reflects_proof x y hx hy separable same

/-- Over a separable bound context, two case trees are natively equal
exactly when they are the same term. -/
theorem caseTree_equiv_iff (separable : Separable β) (p : CaseTree .body β L t) (q : CaseTree .body β L u) :
    Equiv false Γ₀ β t u (packedExitType L) ↔ t = u :=
  ⟨fun h => by
      obtain ⟨ρ, k, sep⟩ := separable
      exact caseTree_eq_of_run p q ρ k sep ((LetCase.Structural.Reply.traceArrow_eq_iff_run p.typing q.typing).mp
        (LetCase.Structural.Reply.traceArrow_of_valid
          (LetCase.Structural.Reply.valid_of_equiv p.typing q.typing h)) ρ),
    fun same => by
      cases same
      exact .refl p.typing.toHasType⟩

/-! ## Branching operands -/

/-- A case tree is a branching operand. -/
theorem branching_operand (p : CaseTree .body β L t) : Branching p.operand :=
  ⟨t, p, .refl p.typing.toHasType⟩

/-- An operand natively equal to a branching operand is branching. -/
theorem Branching.congr {x y : Operand Φ β (packedExitType L)}
    (h : Equiv false Γ₀ β x.1 y.1 (packedExitType L)) (branching : Branching y) : Branching x :=
  let ⟨t, p, same⟩ := branching
  ⟨t, p, h.trans same⟩

/-- The graph read back from a case tree emits a branching operand. -/
theorem branching_graph (p : CaseTree .body β L t) : Branching p.graph.toLetCase :=
  ⟨t, p, CheckedTable.ofLetCase_emit false p.exits_ne_nil p.typing⟩

/-- Entries with branching emitted operands are reflected by the ordered
trace interpretation with atoms. -/
theorem branching_traceReflects (separable : Separable β) (l r : RankedEntry Φ β L)
    (hl : Branching (emitted (P := atomSig α Φ) l)) (hr : Branching (emitted (P := atomSig α Φ) r)) :
    TraceReflects l r :=
  branching_reflects separable _ _ hl hr

/-! ## Soundness and completeness -/

/-- A ranked sentence between entries with branching emitted operands,
over a separable bound context, holds in every supported model of the
ranked room exactly when the emitted operands are natively equal. -/
theorem rankedValid_branching_iff (separable : Separable β) (l r : RankedEntry Φ β L)
    (hl : Branching (emitted (P := atomSig α Φ) l)) (hr : Branching (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      Equiv false Γ₀ β (emitted (P := atomSig α Φ) l).1 (emitted (P := atomSig α Φ) r).1
        (packedExitType L) :=
  (rankedValid_iff_of_traceReflects (sentenceOf l r) (branching_traceReflects separable l r hl hr)).trans
    (derivable_iff false (sentenceOf l r))

/-- Validity of such a sentence is decided by the one ordered trace model
with atoms. -/
theorem rankedValid_branching_iff_atomTrace (separable : Separable β) (l r : RankedEntry Φ β L)
    (hl : Branching (emitted (P := atomSig α Φ) l)) (hr : Branching (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := α) (Φ := Φ)) (atomSig α Φ)).Sat
        (atomTraceRanked α Φ) (sentenceOf l r) :=
  rankedValid_iff_atomTrace (sentenceOf l r) (branching_traceReflects separable l r hl hr)

/-- On the graphs read back from two case trees, validity in the ranked
room is equality of the two trees. The sentence is at the original ordered
exits. -/
theorem rankedValid_caseTree_iff (separable : Separable β) (p : CaseTree .body β L t) (q : CaseTree .body β L u) :
    RankedValid false (sentenceOf (entryOf p.graph) (entryOf q.graph)) ↔ t = u :=
  (rankedValid_branching_iff separable (entryOf p.graph) (entryOf q.graph) (branching_graph p)
    (branching_graph q)).trans
    (Iff.trans
      ⟨fun h => ((CheckedTable.ofLetCase_emit false p.exits_ne_nil p.typing).symm.trans h).trans
          (CheckedTable.ofLetCase_emit false q.exits_ne_nil q.typing),
        fun h => ((CheckedTable.ofLetCase_emit false p.exits_ne_nil p.typing).trans h).trans
          (CheckedTable.ofLetCase_emit false q.exits_ne_nil q.typing).symm⟩
      (caseTree_equiv_iff separable p q))

/-- At the ordered trace model with atoms, the original ordered-exit
arrows of the graphs read back from two case trees are equal exactly when
the trees are the same. The arrows are those of the ranked room, into the
ordered exits, before any packing. -/
theorem denoteRanked_caseTree_iff (separable : Separable β) (p : CaseTree .body β L t) (q : CaseTree .body β L u) :
    denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf p.graph) =
        denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf q.graph) ↔ t = u :=
  (rankedValid_branching_iff_atomTrace separable (entryOf p.graph) (entryOf q.graph) (branching_graph p)
    (branching_graph q)).symm.trans (rankedValid_caseTree_iff separable p q)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

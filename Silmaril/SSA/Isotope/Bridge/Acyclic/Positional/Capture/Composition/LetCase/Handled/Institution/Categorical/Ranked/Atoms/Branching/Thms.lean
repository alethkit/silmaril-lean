module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.AtomBranching

/-! # Completeness for case trees on tagged atom replies

The ordered trace interpretation whose atoms are natural numbers reflects
native equality of branching operands. This is proved, not assumed.

The exits are an ordered list of atom sorts. At an environment that gives
distinct tokens to the atom slots, two case trees with the same ordered
traces are the same term. A leaf is determined by the value it returns:
the value is a token under the injections of one exit position, so it
fixes the position, the sort of the exit and the token, and the token
fixes the slot. Two exits of the same sort are told apart. A request node
is determined by its first logged event, which records the primitive and
the tokens of the argument. The reply may carry either tag with any
payload, so the run of the node contains the runs of both arms at every
payload token. Extending the environment by the next unused token keeps
the atom slots distinct, and the argument continues in each arm.

A ranked sentence between entries whose emitted operands are natively
equal to case trees, over a separable bound context, is therefore valid in
all supported models exactly when the emitted operands are natively equal.
The sentence is at the original ordered exits of the entries. On the
graphs read back from two case trees, validity is equality of the trees,
and so is equality of their ordered-exit arrows at the one model.

The class is exact. Every primitive replies with one atom under one of two
tags, every case is on a request, and each leaf returns one atom slot at
one exit of the same sort. Sequencing without a case, cases on other
scrutinees, payloads that are not atoms and exits that are not atoms are
outside it.
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

variable {α Φ : Type} [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n} {L : List α}

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

/-! ## The reduction at a request node -/

variable {t u : LetCase.LocallyNameless.Tm Empty Φ n}

/-- At a request node with the same primitive and argument, the ordered
traces agree exactly when the arms agree at every payload token. The older
slots keep their values in both arms. -/
theorem ask_run_eq_iff (f : Φ) (argument : Assembly β (instrSrc f))
    {l r l' r' : LetCase.LocallyNameless.Tm Empty Φ (n + 1)}
    (left : CaseTree (β.snoc (.base (TaggedSignature.left f))) L l)
    (right : CaseTree (β.snoc (.base (TaggedSignature.right f))) L r)
    (left' : CaseTree (β.snoc (.base (TaggedSignature.left f))) L l')
    (right' : CaseTree (β.snoc (.base (TaggedSignature.right f))) L r')
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) :
    run (CaseTree.ask f argument left right).typing ρ = run (CaseTree.ask f argument left' right').typing ρ ↔
      (∀ x : Nat, run left.typing (ρ.snoc (A := Ty.base (TaggedSignature.left f)) x) =
        run left'.typing (ρ.snoc (A := Ty.base (TaggedSignature.left f)) x)) ∧
      (∀ y : Nat, run right.typing (ρ.snoc (A := Ty.base (TaggedSignature.right f)) y) =
        run right'.typing (ρ.snoc (A := Ty.base (TaggedSignature.right f)) y)) :=
  ask_run_eq_iff_proof f argument left right left' right' ρ

/-! ## Exits -/

omit [TaggedSignature α Φ] in
/-- The value returned at an exit fixes the sort of the exit, the token
and the position of the exit among the ordered exits. Two exits of the
same sort with the same token are told apart. -/
theorem ExitAt.value_inj {a b : α} (e : ExitAt L a) (e' : ExitAt L b) (x y : Nat)
    (same : e.value x = e'.value y) : a = b ∧ x = y ∧ e.index = e'.index :=
  exit_value_index_proof e e' x y same

/-- A leaf returns the token of its slot at its exit. -/
theorem run_ret {a : α} (exit : ExitAt L a) (s : LetSeq.StraightLine.Structural.Slot β (.base a))
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) :
    run (CaseTree.ret (Φ := Φ) exit s).typing ρ = pure (exit.value (s.value ρ)) :=
  run_ret_proof exit s ρ

/-! ## Separation of case trees -/

/-- Two case trees with the same ordered traces at one environment that
separates the atom slots are the same term. -/
theorem caseTree_eq_of_run (p : CaseTree β L t) (q : CaseTree β L u)
    (ρ : BoundEnv (LetSeq.StraightLine.Structural.Value (α := α)) β) (k : Nat)
    (sep : Separates ρ (Set.Iio k)) (same : run p.typing ρ = run q.typing ρ) : t = u :=
  caseTree_eq_of_run_proof p q ρ k sep same

/-- The ordered trace interpretation with atoms reflects native equality
of branching operands over a separable bound context. -/
theorem branching_reflects (separable : Separable β) (x y : Operand Φ β (packedExitType (exitTypes L)))
    (hx : Branching x) (hy : Branching y) (same : traceArrow x.2 = traceArrow y.2) :
    Equiv false Γ₀ β x.1 y.1 (packedExitType (exitTypes L)) :=
  branching_reflects_proof x y hx hy separable same

/-- Over a separable bound context, two case trees are natively equal
exactly when they are the same term. -/
theorem caseTree_equiv_iff (separable : Separable β) (p : CaseTree β L t) (q : CaseTree β L u) :
    Equiv false Γ₀ β t u (packedExitType (exitTypes L)) ↔ t = u :=
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
theorem branching_operand (p : CaseTree β L t) : Branching p.operand :=
  ⟨t, p, .refl p.typing.toHasType⟩

/-- An operand natively equal to a branching operand is branching. -/
theorem Branching.congr {x y : Operand Φ β (packedExitType (exitTypes L))}
    (h : Equiv false Γ₀ β x.1 y.1 (packedExitType (exitTypes L))) (branching : Branching y) : Branching x :=
  let ⟨t, p, same⟩ := branching
  ⟨t, p, h.trans same⟩

/-- The graph read back from a case tree emits a branching operand. -/
theorem branching_graph (p : CaseTree β L t) : Branching p.graph.toLetCase :=
  ⟨t, p, CheckedTable.ofLetCase_emit false p.exits_ne_nil p.typing⟩

/-- Entries with branching emitted operands are reflected by the ordered
trace interpretation with atoms. -/
theorem branching_traceReflects (separable : Separable β) (l r : RankedEntry Φ β (exitTypes L))
    (hl : Branching (emitted (P := atomSig α Φ) l)) (hr : Branching (emitted (P := atomSig α Φ) r)) :
    TraceReflects l r :=
  branching_reflects separable _ _ hl hr

/-! ## Soundness and completeness -/

/-- A ranked sentence between entries with branching emitted operands,
over a separable bound context, holds in every supported model of the
ranked room exactly when the emitted operands are natively equal. -/
theorem rankedValid_branching_iff (separable : Separable β) (l r : RankedEntry Φ β (exitTypes L))
    (hl : Branching (emitted (P := atomSig α Φ) l)) (hr : Branching (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      Equiv false Γ₀ β (emitted (P := atomSig α Φ) l).1 (emitted (P := atomSig α Φ) r).1
        (packedExitType (exitTypes L)) :=
  (rankedValid_iff_of_traceReflects (sentenceOf l r) (branching_traceReflects separable l r hl hr)).trans
    (derivable_iff false (sentenceOf l r))

/-- Validity of such a sentence is decided by the one ordered trace model
with atoms. -/
theorem rankedValid_branching_iff_atomTrace (separable : Separable β) (l r : RankedEntry Φ β (exitTypes L))
    (hl : Branching (emitted (P := atomSig α Φ) l)) (hr : Branching (emitted (P := atomSig α Φ) r)) :
    RankedValid false (sentenceOf l r) ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := α) (Φ := Φ)) (atomSig α Φ)).Sat
        (atomTraceRanked α Φ) (sentenceOf l r) :=
  rankedValid_iff_atomTrace (sentenceOf l r) (branching_traceReflects separable l r hl hr)

/-- On the graphs read back from two case trees, validity in the ranked
room is equality of the two trees. The sentence is at the original ordered
exits. -/
theorem rankedValid_caseTree_iff (separable : Separable β) (p : CaseTree β L t) (q : CaseTree β L u) :
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
theorem denoteRanked_caseTree_iff (separable : Separable β) (p : CaseTree β L t) (q : CaseTree β L u) :
    denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf p.graph) =
        denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) (entryOf q.graph) ↔ t = u :=
  (rankedValid_branching_iff_atomTrace separable (entryOf p.graph) (entryOf q.graph) (branching_graph p)
    (branching_graph q)).symm.trans (rankedValid_caseTree_iff separable p q)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

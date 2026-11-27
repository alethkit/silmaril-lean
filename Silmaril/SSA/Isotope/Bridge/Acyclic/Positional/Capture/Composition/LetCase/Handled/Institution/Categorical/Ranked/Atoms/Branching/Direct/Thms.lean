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

The covered syntax is exact. A request is followed by one of the three
heads. After a pair head the first atom is a slot and the rest of the
tuple is pending. After a case head each arm has its tuple or the
remaining tags pending. Pending tuples and tags are consumed at once and
in order, as in the case trees. Other placements of a destructuring, and
arbitrary LetCase terms, are outside it.

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
open LetSeq.StraightLine.Structural (Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open scoped LetSeq.StraightLine.Structural Tagged Binary

/-! ## Spelled trees -/

section Spelled

variable {α Φ : Type} [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}
  {t u : LetCase.LocallyNameless.Tm Empty Φ n}

omit [TaggedSignature α Φ] in
/-- Renaming commutes with returning at an exit. -/
theorem ExitAt.term_rename {A : Ty α} (e : ExitAt L A) {m : Nat} (ξ : Fin n → Fin m)
    (t : LetCase.LocallyNameless.Tm Empty Φ n) : (e.term t).rename ξ = e.term (t.rename ξ) :=
  exit_term_rename_proof e ξ t

omit [TaggedSignature α Φ] in
/-- Renaming commutes with assembling a payload or an argument. -/
theorem argTerm_rename {A : Ty α} (p : Assembly β A) {m : Nat} {γ : BoundCtx (Ty α) m}
    (ρ : BoundCtx.Renaming β γ) : (argTerm (Φ := Φ) p).rename ρ.toFun = argTerm (p.rename ρ) :=
  argTerm_rename_proof p ρ

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

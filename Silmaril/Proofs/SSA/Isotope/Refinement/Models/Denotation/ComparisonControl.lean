module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.TypingComparison
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.CaseEquations

/-! # Common semantic typings for instructions and control

Comparison of fixed instruction types reduces to identity transports. Sums
combine the independently chosen hidden summands, and empty elimination uses
the actual initial-object universal property.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {α : Type u} [DecidableEq α] [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : CaseData.{u,v,w,r} (Ty α) Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F)

/-- The two diagonal type comparisons are identity arrows, with their
explicit dependent target equality. -/
theorem mergeLeft_self_heq (A : Ty α) : HEq (mergeLeft M A A) (M.identity A) :=
  PureHom.val_heq M.toSeqModel rfl (mergeType_self A)
    (purePair_components_heq M (mergeType_self A) (mergeArrows_self M A)).1

theorem mergeRight_self_heq (A : Ty α) : HEq (mergeRight M A A) (M.identity A) :=
  PureHom.val_heq M.toSeqModel rfl (mergeType_self A)
    (purePair_components_heq M (mergeType_self A) (mergeArrows_self M A)).2

omit [DecidableEq α] in
/-- Remove an identity comparison after transporting its dependent target. -/
theorem diagonal_square_iff {A B C X : Ty α} (he : X = B)
    (f : M.Hom A B) (g : M.Hom B X) (c : M.Hom A C)
    (l : M.Hom C X) (l' : M.Hom C B)
    (hg : HEq g (M.identity B)) (hl : HEq l l') :
    M.compose f g = M.compose c l ↔ f = M.compose c l' := by
  cases he
  cases eq_of_heq hg
  cases eq_of_heq hl
  rw [M.compose_identity]

/-- A comparison with the same result type can be expressed without a
redundant diagonal merge in its common typing. -/
theorem TypingComparison.diagonal_iff {n : Nat} {Γ Δ : QCtx (Ty α) n} {e e' : ε}
    {t : Term Φ n} {A : Ty α} (h : HasType F Γ e t A) (k : HasType F Δ e' t A)
    (hc : QCtx.Aligned Γ Δ) :
    TypingComparison M K h k hc ↔
      ∃ l : HasType F (QCtx.merge Γ Δ) (⊤ : ε) t A,
        denote M.toSeqData K h = M.compose (mergeContext M Γ Δ hc).1.1 (denote M.toSeqData K l) ∧
        denote M.toSeqData K k = M.compose (mergeContext M Γ Δ hc).2.1 (denote M.toSeqData K l) := by
  constructor
  · rintro ⟨l, hl, hr⟩
    let l' := (mergeType_self A) ▸ l
    have he := (denote_result_transport M.toSeqModel K l (mergeType_self A)).symm
    refine ⟨l', ?_, ?_⟩
    · exact (diagonal_square_iff M (mergeType_self A) _ _ _ _ _ (mergeLeft_self_heq M A) he).mp hl
    · exact (diagonal_square_iff M (mergeType_self A) _ _ _ _ _ (mergeRight_self_heq M A) he).mp hr
  · rintro ⟨l, hl, hr⟩
    let l' := (mergeType_self A).symm ▸ l
    have he := denote_result_transport M.toSeqModel K l (mergeType_self A).symm
    refine ⟨l', ?_, ?_⟩
    · exact (diagonal_square_iff M (mergeType_self A) _ _ _ _ _ (mergeLeft_self_heq M A) he).mpr hl
    · exact (diagonal_square_iff M (mergeType_self A) _ _ _ _ _ (mergeRight_self_heq M A) he).mpr hr

/-- An instruction has fixed input and output types in the signature. -/
theorem TypingComparison.op {n : Nat} {Γ Δ : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} (f : Φ) (hf : instrEff f ≤ e) (kf : instrEff f ≤ e')
    (h : HasType F Γ e a (instrSrc f)) (k : HasType F Δ e' a (instrSrc f))
    (hc : QCtx.Aligned Γ Δ) (c : TypingComparison M K h k hc) :
    TypingComparison M K (.op hf h) (.op kf k) hc := by
  obtain ⟨l, hl, hr⟩ := (TypingComparison.diagonal_iff M K h k hc).mp c
  apply (TypingComparison.diagonal_iff M K _ _ hc).mpr
  refine ⟨.op le_top l, ?_, ?_⟩
  · change M.compose (denote M.toSeqData K h) (M.instruction f) =
      M.compose (mergeContext M Γ Δ hc).1.1 (M.compose (denote M.toSeqData K l) (M.instruction f))
    rw [hl, M.compose_assoc]
  · change M.compose (denote M.toSeqData K k) (M.instruction f) =
      M.compose (mergeContext M Γ Δ hc).2.1 (M.compose (denote M.toSeqData K l) (M.instruction f))
    rw [hr, M.compose_assoc]

variable (it : F.HasIter → ∀ {A B : Ty α}, M.Hom A (coprod B A) → M.Hom A B)
local notation "L" => ControlData.ofCase M F it

/-- The unused right summands are combined covariantly. -/
theorem TypingComparison.inl {n : Nat} {Γ Δ : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {A B C D : Ty α} (cap : F.HasCase)
    (h : HasType F Γ e a A) (k : HasType F Δ e' a C)
    (hc : QCtx.Aligned Γ Δ) (c : TypingComparison M L h k hc) :
    TypingComparison M L (.inl (B := B) cap h) (.inl (B := D) cap k) hc := by
  obtain ⟨l, hl, hr⟩ := c
  refine ⟨.inl cap l, ?_, ?_⟩
  · change M.compose (M.compose (denote M.toSeqData L h) (M.inl A B))
      (M.desc (M.compose (mergeLeft M A C) (M.inl _ _))
        (M.compose (mergeLeft M B D) (M.inr _ _))) =
      M.compose (mergeContext M Γ Δ hc).1.1 (M.compose (denote M.toSeqData L l) (M.inl _ _))
    rw [M.compose_assoc, M.inl_desc, ← M.compose_assoc, hl, M.compose_assoc]
  · change M.compose (M.compose (denote M.toSeqData L k) (M.inl C D))
      (M.desc (M.compose (mergeRight M A C) (M.inl _ _))
        (M.compose (mergeRight M B D) (M.inr _ _))) =
      M.compose (mergeContext M Γ Δ hc).2.1 (M.compose (denote M.toSeqData L l) (M.inl _ _))
    rw [M.compose_assoc, M.inl_desc, ← M.compose_assoc, hr, M.compose_assoc]

/-- The unused left summands are combined covariantly. -/
theorem TypingComparison.inr {n : Nat} {Γ Δ : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {A B C D : Ty α} (cap : F.HasCase)
    (h : HasType F Γ e a B) (k : HasType F Δ e' a D)
    (hc : QCtx.Aligned Γ Δ) (c : TypingComparison M L h k hc) :
    TypingComparison M L (.inr (A := A) cap h) (.inr (A := C) cap k) hc := by
  obtain ⟨l, hl, hr⟩ := c
  refine ⟨.inr cap l, ?_, ?_⟩
  · change M.compose (M.compose (denote M.toSeqData L h) (M.inr A B))
      (M.desc (M.compose (mergeLeft M A C) (M.inl _ _))
        (M.compose (mergeLeft M B D) (M.inr _ _))) =
      M.compose (mergeContext M Γ Δ hc).1.1 (M.compose (denote M.toSeqData L l) (M.inr _ _))
    rw [M.compose_assoc, M.inr_desc, ← M.compose_assoc, hl, M.compose_assoc]
  · change M.compose (M.compose (denote M.toSeqData L k) (M.inr C D))
      (M.desc (M.compose (mergeRight M A C) (M.inl _ _))
        (M.compose (mergeRight M B D) (M.inr _ _))) =
      M.compose (mergeContext M Γ Δ hc).2.1 (M.compose (denote M.toSeqData L l) (M.inr _ _))
    rw [M.compose_assoc, M.inr_desc, ← M.compose_assoc, hr, M.compose_assoc]

/-- Empty elimination is independent of its chosen output type. -/
theorem TypingComparison.abort {n : Nat} {Γ Δ : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {A B : Ty α} (cap : F.HasCase)
    (h : HasType F Γ e a Silmaril.empty) (k : HasType F Δ e' a Silmaril.empty)
    (hc : QCtx.Aligned Γ Δ) (c : TypingComparison M L h k hc) :
    TypingComparison M L (.abort (A := A) cap h) (.abort (A := B) cap k) hc := by
  obtain ⟨l, hl, hr⟩ := (TypingComparison.diagonal_iff M L h k hc).mp c
  refine ⟨.abort cap l, ?_, ?_⟩
  · change M.compose (M.compose (denote M.toSeqData L h) (M.abort A)) (mergeLeft M A B) =
      M.compose (mergeContext M Γ Δ hc).1.1 (M.compose (denote M.toSeqData L l) (M.abort _))
    rw [M.compose_assoc, M.empty_hom_ext (M.compose (M.abort A) (mergeLeft M A B)) (M.abort _),
      hl, M.compose_assoc]
  · change M.compose (M.compose (denote M.toSeqData L k) (M.abort B)) (mergeRight M A B) =
      M.compose (mergeContext M Γ Δ hc).2.1 (M.compose (denote M.toSeqData L l) (M.abort _))
    rw [M.compose_assoc, M.empty_hom_ext (M.compose (M.abort B) (mergeRight M A B)) (M.abort _),
      hr, M.compose_assoc]

end Silmaril.Isotope.Refinement.Models.Denotation

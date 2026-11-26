module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Arguments
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reflection.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case (onHead source_wf)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues
  (ConstructorLeaf Profile)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments.Proofs

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε]
  {Γ Δ : EffectCtx (Ty α) ε} {A B C : Ty α} {e : ε} {a k l r : Expr Φ}

theorem case_eqv_bind [Preorder ε] [OrderBot ε] {s : Expr Φ} (hs : Wf Γ s (.coprod A B) e)
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e) :
    Eqv Γ C e (.case s l r) (.let₁ s (.case (.var 0) l.wk1 r.wk1)) :=
  .step (.rewrite (.case hs hl hr) (.let₁ hs (source_wf hl hr)) (.case_bind _ _ _))

variable [PartialOrder ε] [OrderBot ε]

private abbrev Atomic (Γ : EffectCtx (Ty α) ε) : Prop :=
  ∀ i : Fin Γ.length, ∃ x, (Γ.get i).1 = Ty.base x

/-- A continuation is recognized after any typed constructor substitution
into an atomic context. This includes reply specialization, binder insertion,
and substitution of a known constructor payload. -/
private def Covered (Γ : EffectCtx (Ty α) ε) (A : Ty α) (e : ε) (a : Expr Φ) : Prop :=
  ∀ {Δ : EffectCtx (Ty α) ε} {σ : Nat → Expr Φ}, Atomic Δ →
    (∀ i : Fin Γ.length, Wf Δ (σ i.val) (Γ.get i).1 (Γ.get i).2) →
    (∀ i, ConstructorLeaf (σ i)) → ReplyReflection.Written A e Δ (a.subst σ)

private theorem covered_of_eqv (eq : Eqv Γ A e a k) (h : Covered Γ A e k) :
    Covered Γ A e a :=
  fun atomic ht hs => written_of_eqv (eq.subst_typed ht) (h atomic ht hs)

private theorem covered_subst (h : Covered Γ A e a) {σ : Nat → Expr Φ}
    (ht : ∀ i : Fin Γ.length, Wf Δ (σ i.val) (Γ.get i).1 (Γ.get i).2)
    (hs : ∀ i, ConstructorLeaf (σ i)) : Covered Δ A e (a.subst σ) := by
  intro Ξ θ atomic hw hl
  rw [Expr.subst_comp]
  exact h atomic (fun i => (ht i).subst_typed hw) (fun i => leaf_subst (hs i) hl)

private theorem wk1_typed (R : Ty α) (h : Wf ((A, ⊥) :: Γ) k B e) :
    Wf ((A, ⊥) :: (R, ⊥) :: Γ) k.wk1 B e := by
  rw [Expr.wk1, Expr.wk_eq_subst]
  exact h.subst_typed (wk1_subst_typed R)

private theorem covered_wk1 (R : Ty α) (h : Covered ((A, ⊥) :: Γ) B e k) :
    Covered ((A, ⊥) :: (R, ⊥) :: Γ) B e k.wk1 := by
  rw [Expr.wk1, Expr.wk_eq_subst]
  exact covered_subst h (wk1_subst_typed R) (fun _ => .var _)

omit [HasTy Φ (Ty α)] [HasEff Φ ε] in
private theorem atomic_fields (atomic : Atomic Γ) {n : Nat} (sorts : Fin n → α) :
    Atomic (ReplyShape.fieldCtx sorts Γ) := by
  intro i
  refine Fin.addCases (motive := fun j => ∃ x,
    ((ReplyShape.fieldCtx sorts Γ).get (j.cast (ReplyShape.fieldCtx_length sorts Γ).symm)).1 =
      Ty.base x) ?_ ?_ (i.cast (ReplyShape.fieldCtx_length sorts Γ))
  · intro j
    exact ⟨sorts j, congrArg Prod.fst (ReplyShape.get_fieldIndex j)⟩
  · intro j
    have get := ReplyShape.get_ambientIndex (sorts := sorts) j
    obtain ⟨x, hx⟩ := atomic j
    exact ⟨x, (congrArg Prod.fst get).trans hx⟩

private theorem covered_call {f : Φ} {arg : Expr Φ}
    (visible : ¬ IsPure (⊥ : ε) f) (bound : instrEff f ≤ e)
    (typed : Wf Γ arg (instrSrc f) ⊥) (leaf : ConstructorLeaf arg)
    (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e) (body : Covered ((instrTrg f, ⊥) :: Γ) A e k) :
    Covered Γ A e (.let₁ (.op f arg) k) := by
  intro Δ σ atomic ht hs
  refine ReplyReflection.Written.of_call visible bound (typed.subst_typed ht) (leaf_subst leaf hs)
    (hk.subst_typed (lift_typed ht _)) ?_
  intro n sorts shape
  rw [ReplyShape.specialize, Expr.subst_comp]
  exact body (atomic_fields atomic sorts)
    (fun i => (lift_typed ht _ i).subst_typed (shape_subst_typed shape))
    (fun i => leaf_subst (lift_leaf hs i) (shape_subst_leaf shape))

private theorem covered_bind (ha : Sequenced e Γ A a) (hk : Wf ((A, ⊥) :: Γ) k B e)
    (body : Covered ((A, ⊥) :: Γ) B e k) :
    Covered Γ B e (.let₁ a k) := by
  induction ha generalizing k with
  | leaf typed leaf =>
      exact covered_of_eqv (.step (.let1_beta typed hk))
        (covered_subst body (subst0_typed typed) (subst0_leaf leaf))
  | @call Γ' X f arg p visible bound typed leaf bodySeq ih =>
      have req := Wf.op bound (typed.weakenEffect bot_le)
      have hp := sequenced_wf bodySeq
      have hw := wk1_typed (instrTrg f) hk
      have head := Eqv.step (.rewrite (.let₁ (.let₁ req hp) hk)
        (.let₁ req (.let₁ hp hw)) (.let1_let1 _ _ _))
      intro Δ σ atomic ht hs
      exact covered_of_eqv head
        (covered_call visible bound typed leaf (.let₁ hp hw) (ih hw (covered_wk1 (instrTrg f) body)))
        atomic ht hs

private theorem leaf_sum {s : Expr Φ} (profile : Profile (α := α) Φ ε) (atomic : Atomic Γ)
    (leaf : ConstructorLeaf s) (typed : Wf Γ s (.coprod A B) (⊥ : ε)) :
    (∃ p, s = .inl p ∧ Wf Γ p A (⊥ : ε) ∧ ConstructorLeaf p) ∨
    (∃ p, s = .inr p ∧ Wf Γ p B (⊥ : ε) ∧ ConstructorLeaf p) := by
  generalize hsum : Ty.coprod A B = S at typed
  cases leaf with
  | var j =>
      cases typed with
      | var i _ =>
          obtain ⟨x, hx⟩ := atomic i
          rw [hx] at hsum
          cases hsum
  | op leaf =>
      cases typed with
      | op bound _ =>
          have pure : IsPure (⊥ : ε) _ := le_antisymm bound bot_le
          cases profile _ pure with
          | atom x eq =>
              rw [eq] at hsum
              cases hsum
          | unit eq =>
              rw [eq] at hsum
              cases hsum
  | unit =>
      cases typed
      cases hsum
  | pair _ _ =>
      cases typed
      cases hsum
  | inl leaf =>
      cases typed with
      | inl p =>
          cases hsum
          exact .inl ⟨_, rfl, p, leaf⟩
  | inr leaf =>
      cases typed with
      | inr p =>
          cases hsum
          exact .inr ⟨_, rfl, p, leaf⟩

private theorem covered_case (profile : Profile (α := α) Φ ε)
    (ht : Wf Γ a (.coprod A B) (⊥ : ε)) (leaf : ConstructorLeaf a)
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e)
    (cl : Covered ((A, ⊥) :: Γ) C e l) (cr : Covered ((B, ⊥) :: Γ) C e r) :
    Covered Γ C e (.case a l r) := by
  intro Δ σ atomic hσ leaves
  change ReplyReflection.Written C e Δ
    (.case (a.subst σ) (l.subst (Expr.liftSubst σ)) (r.subst (Expr.liftSubst σ)))
  have left := hl.subst_typed (lift_typed hσ _)
  have right := hr.subst_typed (lift_typed hσ _)
  obtain ⟨p, tag, typed, pl⟩ | ⟨p, tag, typed, pl⟩ :=
    leaf_sum profile atomic (leaf_subst leaf leaves) (ht.subst_typed hσ)
  · rw [tag]
    have beta := Eqv.step (.reduce (.case (.inl (typed.weakenEffect bot_le)) left right)
      (.let₁ (typed.weakenEffect bot_le) left) (.case_inl _ _ _))
    exact written_of_eqv (beta.trans (.step (.let1_beta typed left)))
      (covered_subst cl (lift_typed hσ _) (lift_leaf leaves) atomic (subst0_typed typed) (subst0_leaf pl))
  · rw [tag]
    have beta := Eqv.step (.reduce (.case (.inr (typed.weakenEffect bot_le)) left right)
      (.let₁ (typed.weakenEffect bot_le) right) (.case_inr _ _ _))
    exact written_of_eqv (beta.trans (.step (.let1_beta typed right)))
      (covered_subst cr (lift_typed hσ _) (lift_leaf leaves) atomic (subst0_typed typed) (subst0_leaf pl))

private theorem case_raw_covered (profile : Profile (α := α) Φ ε) (h : CaseRaw e Γ A a) :
    Wf Γ a A e ∧ Covered Γ A e a := by
  induction h with
  | straight raw =>
      obtain ⟨_, eq, seq⟩ := normalize raw
      exact ⟨eq.endpoints_wf.1, covered_of_eqv eq (fun _ => written_subst seq)⟩
  | let1 raw _ ih =>
      obtain ⟨_, eq, seq⟩ := normalize raw
      exact ⟨.let₁ eq.endpoints_wf.1 ih.1,
        covered_of_eqv (.let1 eq (.refl ih.1)) (covered_bind seq ih.1 ih.2)⟩
  | @case Γ' X Y Z s l r raw _ _ il ir =>
      obtain ⟨p, eq, seq⟩ := normalize raw
      have hp := sequenced_wf seq
      have hk := source_wf il.1 ir.1
      have bind := case_eqv_bind hp il.1 ir.1
      have body : Covered ((Ty.coprod X Y, ⊥) :: Γ') Z e (onHead l r) :=
        covered_case profile (.var 0 le_rfl) (.var 0) (wk1_typed _ il.1) (wk1_typed _ ir.1)
          (covered_wk1 _ il.2) (covered_wk1 _ ir.2)
      exact ⟨.case eq.endpoints_wf.1 il.1 ir.1,
        covered_of_eqv ((Eqv.case eq (.refl il.1) (.refl ir.1)).trans bind) (covered_bind seq hk body)⟩

theorem case_raw_written (profile : Profile (α := α) Φ ε)
    (atomic : ∀ i : Fin Γ.length, ∃ x, (Γ.get i).1 = Ty.base x) (h : CaseRaw e Γ A a) :
    ReplyReflection.Written A e Γ a := by
  have cover : Covered Γ A e a := (case_raw_covered profile h).2
  simpa only [Expr.subst_var] using cover (σ := Expr.var) atomic (fun i => .var i le_rfl) .var

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments.Proofs

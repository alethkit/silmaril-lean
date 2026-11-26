module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.ConstructorCover.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.CallByValue.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.ConstructorCover.Proofs

universe u v w

variable {α : Type u} {Φ : Type v} {ε : Type w}
  {Γ : EffectCtx (Ty α) ε} {a b : Expr Φ}

public theorem Value.subst (h : Value a) {σ : Nat → Expr Φ} (hs : ∀ i, Value (σ i)) :
    Value (a.subst σ) := by
  induction h with
  | var i => exact hs i
  | unit => exact .unit
  | pair _ _ left right => exact .pair left right
  | inl _ inner => exact .inl inner
  | inr _ inner => exact .inr inner

section Existence

variable [Preorder ε] [OrderBot ε]

private theorem cover_of_size (size : Nat) :
    ∀ (Γ : EffectCtx (Ty α) ε), ContextReflection.Proofs.contextNodes Γ = size → Γ.Pure →
      Nonempty (ConstructorCover Γ) := by
  classical
  induction size using Nat.strong_induction_on with
  | ind size ih =>
    intro Γ hsize hΓ
    by_cases atomic : ∀ i : Fin Γ.length, ∃ x, (Γ.get i).1 = .base x
    · exact ⟨.atomic atomic⟩
    · obtain ⟨i, hi⟩ := not_forall.mp atomic
      cases ht : (Γ.get i).1 with
      | base x => exact (hi ⟨x, ht⟩).elim
      | empty => exact ⟨.empty i ht (hΓ i)⟩
      | unit =>
        have hlt := hsize ▸ ContextReflection.Proofs.unit_decreases i ht
        obtain ⟨p⟩ := ih _ hlt _ rfl (UnitSlot.eraseCtx_pure hΓ i)
        exact ⟨.unit i ht (hΓ i) p⟩
      | product A B =>
        have hlt := hsize ▸ ContextReflection.Proofs.product_decreases i ht
        obtain ⟨p⟩ := ih _ hlt _ rfl (ProductSplit.splitCtx_pure hΓ i A B)
        exact ⟨.product i ht (hΓ i) p⟩
      | coprod A B =>
        have hl := hsize ▸ ContextReflection.Proofs.sum_left_decreases i ht
        have hr := hsize ▸ ContextReflection.Proofs.sum_right_decreases i ht
        obtain ⟨l⟩ := ih _ hl _ rfl (SumSplit.branchCtx_pure hΓ i A)
        obtain ⟨r⟩ := ih _ hr _ rfl (SumSplit.branchCtx_pure hΓ i B)
        exact ⟨.sum i ht (hΓ i) l r⟩

public theorem exists_cover (hΓ : Γ.Pure) : Nonempty (ConstructorCover Γ) :=
  cover_of_size (ContextReflection.Proofs.contextNodes Γ) Γ rfl hΓ

end Existence

variable [HasTy Φ (Ty α)] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {A : Ty α} {e : ε}

public theorem eqv_render (cover : ConstructorCover Γ) (ha : Wf Γ a A e)
    {leaf : EffectCtx (Ty α) ε → Expr Φ → Expr Φ}
    (h : cover.AllLeaves (fun Δ x => Wf Δ x A e → Eqv Δ A e x (leaf Δ x)) a) :
    Eqv Γ A e a (cover.render leaf a) := by
  induction cover generalizing a with
  | atomic _ => exact h ha
  | empty i ht he =>
    have hv : Wf _ (.var i.val : Expr Φ) (.empty : Ty α) e := ht ▸ Wf.var i (he.trans_le bot_le)
    exact eqv_of_empty_slot i ht he ha (.abort hv)
  | unit i ht he _ ih =>
    have next := ih (UnitSlot.wf_specializeUnit i ht he ha) h
    exact (UnitSlot.unit_eta_rebuild i ht he ha).trans (UnitSlot.eqv_insertUnit i next)
  | product i ht he _ ih =>
    have next := ih (ProductSplit.wf_split i ht he ha) h
    exact (ProductSplit.eqv_rebuild i ht he ha).trans (ProductSplit.eqv_pairLet i ht he next)
  | sum i ht he l r ihL ihR =>
    obtain ⟨hwl, hwr⟩ := SumSplit.wf_specializations i ht he ha
    have hl := ihL hwl h.1
    have hr := ihR hwr h.2
    exact (SumSplit.eqv_rebuild i ht he ha).trans
      ((SumSplit.caseArms_eqv_iff i ht he hwl hwr hl.endpoints_wf.2 hr.endpoints_wf.2).mpr ⟨hl, hr⟩)

omit [HasTy Φ (Ty α)] [HasEff Φ ε] in
private theorem allLeaves_of (cover : ConstructorCover Γ)
    {P : EffectCtx (Ty α) ε → Expr Φ → Prop} (h : ∀ Δ x, P Δ x) :
    cover.AllLeaves P a := by
  induction cover generalizing a with
  | atomic _ => exact h _ _
  | empty _ _ _ => trivial
  | unit _ _ _ _ ih => exact ih
  | product _ _ _ _ ih => exact ih
  | sum _ _ _ _ _ ihL ihR => exact ⟨ihL, ihR⟩

public theorem eqv_rebuild (cover : ConstructorCover Γ) (ha : Wf Γ a A e) :
    Eqv Γ A e a (cover.render (fun _ x => x) a) :=
  eqv_render cover ha (allLeaves_of cover (fun _ _ => Eqv.refl))

private theorem Value.wf_bot (h : Value a) (hΓ : Γ.Pure) (ha : Wf Γ a A e) : Wf Γ a A ⊥ := by
  induction h generalizing A with
  | var i =>
    cases ha with
    | var i _ => exact .var i (hΓ i).le
  | unit =>
    cases ha
    exact .unit _ _
  | pair _ _ ihL ihR =>
    cases ha with
    | pair hl hr => exact .pair (ihL hl) (ihR hr)
  | inl _ ih =>
    cases ha with
    | inl ha => exact .inl (ih ha)
  | inr _ ih =>
    cases ha with
    | inr ha => exact .inr (ih ha)

private theorem unitSubst_value (i j : Nat) : Value (UnitSlot.unitSubst i j : Expr Φ) := by
  unfold UnitSlot.unitSubst
  split
  · exact .unit
  · exact .var _

private theorem splitSubst_value (i j : Nat) : Value (ProductSplit.splitSubst i j : Expr Φ) := by
  unfold ProductSplit.splitSubst
  split
  · exact .pair (.var _) (.var _)
  · exact .var _

private theorem replaceVar_value (i : Nat) (hp : Value b) (j : Nat) :
    Value (SumSplit.replaceVar i b j) := by
  unfold SumSplit.replaceVar
  split
  · exact hp
  · exact .var _

public theorem primitive_leaves (cover : ConstructorCover Γ) (hΓ : Γ.Pure) (f : Φ)
    (ha : Wf Γ a (instrSrc f) e) (hv : Value a) :
    cover.AllLeaves
      (fun Δ request => ∃ v, request = .op f v ∧ Value v ∧ Wf Δ v (instrSrc f) ⊥)
      (.op f a) := by
  induction cover generalizing a with
  | atomic _ => exact ⟨a, rfl, hv, Value.wf_bot hv hΓ ha⟩
  | empty _ _ _ => trivial
  | unit i ht he _ ih =>
    exact ih (UnitSlot.eraseCtx_pure hΓ i) (UnitSlot.wf_specializeUnit i ht he ha)
      (Value.subst hv (unitSubst_value i))
  | product i ht he _ ih =>
    exact ih (ProductSplit.splitCtx_pure hΓ i _ _) (ProductSplit.wf_split i ht he ha)
      (Value.subst hv (splitSubst_value i))
  | sum i ht he _ _ ihL ihR =>
    obtain ⟨hl, hr⟩ := SumSplit.wf_specializations i ht he ha
    exact ⟨ihL (SumSplit.branchCtx_pure hΓ i _) hl (Value.subst hv (replaceVar_value i (.inl (.var i)))),
      ihR (SumSplit.branchCtx_pure hΓ i _) hr (Value.subst hv (replaceVar_value i (.inr (.var i))))⟩

private theorem pure_cons (hΓ : Γ.Pure) (B : Ty α) : EffectCtx.Pure ((B, ⊥) :: Γ) :=
  fun i => Fin.cases rfl (fun j => hΓ j) i

public theorem factor_primitive (hΓ : Γ.Pure) {f : Φ} (hf : instrEff f ≤ e)
    {arg k : Expr Φ} (ha : Wf Γ arg (instrSrc f) e)
    (hk : Wf ((instrTrg f, ⊥) :: Γ) k A e) :
    ∃ input : ConstructorCover ((instrSrc f, ⊥) :: Γ),
    ∃ reply : ConstructorCover ((instrTrg f, ⊥) :: Γ),
      input.AllLeaves
        (fun Δ request => ∃ v, request = .op f v ∧ Value v ∧ Wf Δ v (instrSrc f) ⊥)
        (.op f (.var 0)) ∧
      Eqv Γ A e (.let₁ (.op f arg) k)
        (.let₁ (.let₁ arg (input.render (fun _ x => x) (.op f (.var 0))))
          (reply.render (fun _ x => x) k)) := by
  have hin := pure_cons hΓ (instrSrc f)
  obtain ⟨input⟩ := exists_cover hin
  obtain ⟨reply⟩ := exists_cover (pure_cons hΓ (instrTrg f))
  have hv : Wf ((instrSrc f, ⊥) :: Γ) (.var 0 : Expr Φ) (instrSrc f) e := .var 0 bot_le
  have hcall := (CallByValue.op_bind hf ha).trans
    (Eqv.let1 (.refl ha) (eqv_rebuild input (.op hf hv)))
  exact ⟨input, reply, primitive_leaves input hin f hv (.var 0), .let1 hcall (eqv_rebuild reply hk)⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection.ConstructorCover.Proofs

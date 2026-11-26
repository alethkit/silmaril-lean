module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Arguments
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reflection.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.CallByValue.Thms

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Case (onHead source_wf)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues
  (ConstructorLeaf Profile)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments.Proofs

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε]
  {Γ Δ : EffectCtx (Ty α) ε} {A B C : Ty α} {e : ε} {a b k l r : Expr Φ}

theorem case_eqv_bind [Preorder ε] [OrderBot ε] {s : Expr Φ} (hs : Wf Γ s (.coprod A B) e)
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e) :
    Eqv Γ C e (.case s l r) (.let₁ s (.case (.var 0) l.wk1 r.wk1)) :=
  .step (.rewrite (.case hs hl hr) (.let₁ hs (source_wf hl hr)) (.case_bind _ _ _))

private theorem wk1_typed [Preorder ε] [OrderBot ε] (R : Ty α) (h : Wf ((A, ⊥) :: Γ) k B e) :
    Wf ((A, ⊥) :: (R, ⊥) :: Γ) k.wk1 B e := by
  rw [Expr.wk1, Expr.wk_eq_subst]
  exact h.subst_typed (wk1_subst_typed R)

theorem let_case_eqv [Preorder ε] [OrderBot ε] {D : Ty α}
    (hs : Wf Γ a (.coprod A B) e)
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e)
    (hk : Wf ((C, ⊥) :: Γ) k D e) :
    Eqv Γ D e (.let₁ (.case a l r) k) (.case a (.let₁ l k.wk1) (.let₁ r k.wk1)) :=
  .step (.rewrite (.let₁ (.case hs hl hr) hk)
    (.case hs (.let₁ hl (wk1_typed A hk)) (.let₁ hr (wk1_typed B hk))) (.let1_case _ _ _ _))

private theorem let_assoc_eqv [Preorder ε] [OrderBot ε] {b : Expr Φ}
    (ha : Wf Γ a A e) (hb : Wf ((A, ⊥) :: Γ) b B e)
    (hk : Wf ((B, ⊥) :: Γ) k C e) :
    Eqv Γ C e (.let₁ (.let₁ a b) k) (.let₁ a (.let₁ b k.wk1)) :=
  .step (.rewrite (.let₁ (.let₁ ha hb) hk) (.let₁ ha (.let₁ hb (wk1_typed A hk))) (.let1_let1 _ _ _))

private theorem wk2_subst_typed [Preorder ε] [OrderBot ε] (R : Ty α) :
    ∀ i : Fin ((B, (⊥ : ε)) :: (A, ⊥) :: Γ).length,
      Wf ((B, ⊥) :: (A, ⊥) :: (R, ⊥) :: Γ)
        (Expr.var (Expr.liftWk (Expr.liftWk Nat.succ) i.val) : Expr Φ)
        (((B, (⊥ : ε)) :: (A, ⊥) :: Γ).get i).1 (((B, (⊥ : ε)) :: (A, ⊥) :: Γ).get i).2 := by
  intro i
  refine Fin.cases (.var 0 le_rfl) (fun j => ?_) i
  refine Fin.cases (.var 1 le_rfl) (fun t => ?_) j
  exact Wf.var (Γ := (B, ⊥) :: (A, ⊥) :: (R, ⊥) :: Γ) t.succ.succ.succ le_rfl

private theorem wk2_typed [Preorder ε] [OrderBot ε] (R : Ty α)
    (h : Wf ((B, ⊥) :: (A, ⊥) :: Γ) k C e) :
    Wf ((B, ⊥) :: (A, ⊥) :: (R, ⊥) :: Γ) k.wk2 C e := by
  rw [Expr.wk2, Expr.wk_eq_subst]
  exact h.subst_typed (wk2_subst_typed R)

theorem let2_bind_eqv [Preorder ε] [OrderBot ε] (ha : Wf Γ a (.product A B) e)
    (hk : Wf ((B, ⊥) :: (A, ⊥) :: Γ) k C e) :
    Eqv Γ C e (.let₂ a k) (.let₁ a (.let₂ (.var 0) k.wk2)) :=
  .step (.rewrite (.let₂ ha hk) (.let₁ ha (.let₂ (.var 0 bot_le) (wk2_typed _ hk))) (.let2_bind _ _))

theorem let2_pair_eqv [Preorder ε] [OrderBot ε] (ha : Wf Γ a A e) (hb : Wf Γ b B e)
    (hk : Wf ((B, ⊥) :: (A, ⊥) :: Γ) k C e) :
    Eqv Γ C e (.let₂ (.pair a b) k) (.let₁ a (.let₁ b.wk0 k)) :=
  .step (.rewrite (.let₂ (.pair ha hb) hk)
    (.let₁ ha (.let₁ (CallByValue.wf_wk0 hb (A, ⊥)) hk)) (.let2_pair _ _ _))

private theorem let_let2_eqv [Preorder ε] [OrderBot ε] {D : Ty α}
    (ha : Wf Γ a (.product A B) e) (hb : Wf ((B, ⊥) :: (A, ⊥) :: Γ) b C e)
    (hk : Wf ((C, ⊥) :: Γ) k D e) :
    Eqv Γ D e (.let₁ (.let₂ a b) k) (.let₂ a (.let₁ b k.wk1.wk1)) :=
  .step (.rewrite (.let₁ (.let₂ ha hb) hk)
    (.let₂ ha (.let₁ hb (wk1_typed B (wk1_typed A hk)))) (.let1_let2 _ _ _))

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

private theorem covered_wk1 (R : Ty α) (h : Covered ((A, ⊥) :: Γ) B e k) :
    Covered ((A, ⊥) :: (R, ⊥) :: Γ) B e k.wk1 := by
  rw [Expr.wk1, Expr.wk_eq_subst]
  exact covered_subst h (wk1_subst_typed R) (fun _ => .var _)

private theorem covered_wk2 (R : Ty α) (h : Covered ((B, ⊥) :: (A, ⊥) :: Γ) C e k) :
    Covered ((B, ⊥) :: (A, ⊥) :: (R, ⊥) :: Γ) C e k.wk2 := by
  rw [Expr.wk2, Expr.wk_eq_subst]
  exact covered_subst h (wk2_subst_typed R) (fun _ => .var _)

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
      have head := let_assoc_eqv req hp hk
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

private theorem leaf_product (profile : Profile (α := α) Φ ε) (atomic : Atomic Γ)
    (leaf : ConstructorLeaf a) (typed : Wf Γ a (.product A B) (⊥ : ε)) :
    ∃ p q, a = .pair p q ∧ Wf Γ p A (⊥ : ε) ∧ Wf Γ q B (⊥ : ε) ∧
      ConstructorLeaf p ∧ ConstructorLeaf q := by
  generalize hprod : Ty.product A B = P at typed
  cases leaf with
  | var _ =>
      cases typed with
      | var i _ =>
          obtain ⟨x, hx⟩ := atomic i
          rw [hx] at hprod
          cases hprod
  | op _ =>
      cases typed with
      | op bound _ =>
          have pure : IsPure (⊥ : ε) _ := le_antisymm bound bot_le
          cases profile _ pure with
          | atom x eq =>
              rw [eq] at hprod
              cases hprod
          | unit eq =>
              rw [eq] at hprod
              cases hprod
  | unit =>
      cases typed
      cases hprod
  | inl _ =>
      cases typed
      cases hprod
  | inr _ =>
      cases typed
      cases hprod
  | pair pl ql =>
      cases typed with
      | pair hp hq =>
          cases hprod
          exact ⟨_, _, rfl, hp, hq, pl, ql⟩

private theorem covered_let2 (profile : Profile (α := α) Φ ε)
    (ht : Wf Γ a (.product A B) (⊥ : ε)) (leaf : ConstructorLeaf a)
    (hk : Wf ((B, ⊥) :: (A, ⊥) :: Γ) k C e) (body : Covered ((B, ⊥) :: (A, ⊥) :: Γ) C e k) :
    Covered Γ C e (.let₂ a k) := by
  intro Δ σ atomic hσ leaves
  change ReplyReflection.Written C e Δ (.let₂ (a.subst σ) (k.subst (Expr.liftSubst (Expr.liftSubst σ))))
  have hslot := lift_typed (lift_typed hσ (A, ⊥)) (B, ⊥)
  have fields := hk.subst_typed hslot
  have code : Covered ((B, ⊥) :: (A, ⊥) :: Δ) C e (k.subst (Expr.liftSubst (Expr.liftSubst σ))) :=
    covered_subst body hslot (lift_leaf (lift_leaf leaves))
  obtain ⟨p, q, eq, hp, hq, pl, ql⟩ :=
    leaf_product profile atomic (leaf_subst leaf leaves) (ht.subst_typed hσ)
  rw [eq]
  have qw := CallByValue.wf_wk0 hq (A, ⊥)
  have afterLeft : Covered ((A, ⊥) :: Δ) C e (.let₁ q.wk0 (k.subst (Expr.liftSubst (Expr.liftSubst σ)))) :=
    covered_bind (.leaf qw (leaf_wk ql Nat.succ)) fields code
  have afterBoth : Covered Δ C e (.let₁ p (.let₁ q.wk0 (k.subst (Expr.liftSubst (Expr.liftSubst σ))))) :=
    covered_bind (.leaf hp pl) (.let₁ (qw.weakenEffect bot_le) fields) afterLeft
  have step := let2_pair_eqv (hp.weakenEffect bot_le) (hq.weakenEffect bot_le) fields
  apply written_of_eqv step
  simpa only [Expr.subst_var] using afterBoth (σ := Expr.var) atomic (fun i => .var i le_rfl) .var

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

/-- A computation can expose its calls before any covered continuation.
The result binder retains its original type as the local context grows. -/
private def CoversBind (Γ : EffectCtx (Ty α) ε) (A : Ty α) (e : ε) (a : Expr Φ) : Prop :=
  ∀ {B : Ty α} {k : Expr Φ}, Wf ((A, ⊥) :: Γ) k B e →
    Covered ((A, ⊥) :: Γ) B e k → Covered Γ B e (.let₁ a k)

private theorem covered_case_bind (profile : Profile (α := α) Φ ε)
    (hs : Wf Γ a (.coprod A B) e) (scrutinee : CoversBind Γ (.coprod A B) e a)
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e)
    (cl : Covered ((A, ⊥) :: Γ) C e l) (cr : Covered ((B, ⊥) :: Γ) C e r) :
    Covered Γ C e (.case a l r) := by
  have body : Covered ((Ty.coprod A B, ⊥) :: Γ) C e (onHead l r) :=
    covered_case profile (.var 0 le_rfl) (.var 0) (wk1_typed _ hl) (wk1_typed _ hr)
      (covered_wk1 _ cl) (covered_wk1 _ cr)
  intro Δ σ atomic ht leaves
  exact covered_of_eqv (case_eqv_bind hs hl hr) (scrutinee (source_wf hl hr) body)
    atomic ht leaves

private theorem covered_let2_bind (profile : Profile (α := α) Φ ε)
    (ha : Wf Γ a (.product A B) e) (init : CoversBind Γ (.product A B) e a)
    (hk : Wf ((B, ⊥) :: (A, ⊥) :: Γ) k C e) (body : Covered ((B, ⊥) :: (A, ⊥) :: Γ) C e k) :
    Covered Γ C e (.let₂ a k) := by
  intro Δ σ atomic hσ leaves
  have var : Wf ((Ty.product A B, ⊥) :: Γ) (.var 0 : Expr Φ) (.product A B) ⊥ := .var 0 le_rfl
  have hw := wk2_typed (Ty.product A B) hk
  exact covered_of_eqv (let2_bind_eqv ha hk) (init (.let₂ (var.weakenEffect bot_le) hw)
    (covered_let2 profile var (.var 0) hw (covered_wk2 (Ty.product A B) body))) atomic hσ leaves

/-- Keep the induction stable under typed constructor substitutions. In the
pair case, the right operand is interpreted after weakening its substitution
past the slot retaining the left result. -/
private theorem case_raw_coversBind (profile : Profile (α := α) Φ ε) (h : CaseRaw e Γ A a)
    {σ : Nat → Expr Φ}
    (ht : ∀ i : Fin Γ.length, Wf Δ (σ i.val) (Γ.get i).1 (Γ.get i).2)
    (hs : ∀ i, ConstructorLeaf (σ i)) :
    Wf Δ (a.subst σ) A e ∧ CoversBind Δ A e (a.subst σ) := by
  induction h generalizing Δ σ with
  | straight raw =>
      obtain ⟨_, eq, seq⟩ := normalize raw
      have eq' := eq.subst_typed ht
      refine ⟨eq'.endpoints_wf.1, ?_⟩
      intro B k hk rest
      exact covered_of_eqv (.let1 eq' (.refl hk)) (covered_bind (sequenced_subst seq ht hs) hk rest)
  | @bind Γ' X Y a k _ _ ia ik =>
      obtain ⟨ha, ca⟩ := ia ht hs
      obtain ⟨hk, ck⟩ := ik (lift_typed ht (X, ⊥)) (lift_leaf hs)
      refine ⟨.let₁ ha hk, ?_⟩
      intro Z tail htail rest Ξ θ atomic hθ leaves
      have hw := wk1_typed X htail
      exact covered_of_eqv (let_assoc_eqv ha hk htail)
        (ca (.let₁ hk hw) (ck hw (covered_wk1 X rest))) atomic hθ leaves
  | @branch Γ' X Y Z s l r _ _ _ is il ir =>
      obtain ⟨hs', cs⟩ := is ht hs
      obtain ⟨hl, cl⟩ := il (lift_typed ht (X, ⊥)) (lift_leaf hs)
      obtain ⟨hr, cr⟩ := ir (lift_typed ht (Y, ⊥)) (lift_leaf hs)
      refine ⟨.case hs' hl hr, ?_⟩
      intro D k hk rest Ξ θ atomic hθ leaves
      have kl := wk1_typed X hk
      have kr := wk1_typed Y hk
      exact covered_of_eqv (let_case_eqv hs' hl hr hk)
        (covered_case_bind profile hs' cs (.let₁ hl kl) (.let₁ hr kr)
          (cl kl (covered_wk1 X rest)) (cr kr (covered_wk1 Y rest))) atomic hθ leaves
  | @call Γ' f a visible bound _ ia =>
      obtain ⟨ha, ca⟩ := ia ht hs
      refine ⟨.op bound ha, ?_⟩
      intro B k hk rest Ξ θ atomic hθ leaves
      have arg : Wf ((instrSrc f, ⊥) :: Δ) (.var 0 : Expr Φ) (instrSrc f) ⊥ := .var 0 le_rfl
      have request := Wf.op (f := f) bound (arg.weakenEffect bot_le)
      have hk' := wk1_typed (instrSrc f) hk
      have seq := (Eqv.let1 (CallByValue.op_bind bound ha) (.refl hk)).trans
        (let_assoc_eqv ha request hk)
      exact covered_of_eqv seq
        (ca (.let₁ request hk') (covered_call visible bound arg (.var 0) hk'
          (covered_wk1 (instrSrc f) rest))) atomic hθ leaves
  | @pair Γ' X Y a b _ _ ia ib =>
      obtain ⟨ha, ca⟩ := ia ht hs
      have hb := (ib ht hs).1
      have right : Wf ((X, ⊥) :: Δ) (b.subst σ).wk0 Y e ∧
          CoversBind ((X, ⊥) :: Δ) Y e (b.subst σ).wk0 := by
        rw [Expr.wk0, Expr.wk_subst]
        exact ib (fun i => CallByValue.wf_wk0 (ht i) (X, ⊥))
          (fun i => leaf_wk (hs i) Nat.succ)
      refine ⟨.pair ha hb, ?_⟩
      intro Z k hk rest Ξ θ atomic hθ leaves
      have value : Wf ((Y, ⊥) :: (X, ⊥) :: Δ) (.pair (.var 1) (.var 0) : Expr Φ) (.product X Y) ⊥ :=
        .pair (.var 1 le_rfl) (.var 0 le_rfl)
      have k' := wk1_typed X hk
      have k'' := wk1_typed Y k'
      have tail : Covered ((Y, ⊥) :: (X, ⊥) :: Δ) Z e (.let₁ (.pair (.var 1) (.var 0)) k.wk1.wk1) :=
        covered_bind (.leaf value (.pair (.var 1) (.var 0))) k'' (covered_wk1 Y (covered_wk1 X rest))
      have eq := (Eqv.let1 (CallByValue.pair_bind ha hb) (.refl hk)).trans
        ((let_assoc_eqv ha (.let₁ right.1 (value.weakenEffect bot_le)) hk).trans
          (.let1 (.refl ha) (let_assoc_eqv right.1 (value.weakenEffect bot_le) k')))
      exact covered_of_eqv eq
        (ca (.let₁ right.1 (.let₁ (value.weakenEffect bot_le) k'')) (right.2
          (.let₁ (value.weakenEffect bot_le) k'') tail)) atomic hθ leaves
  | @let2 Γ' X Y Z a k _ _ ia ik =>
      obtain ⟨ha, ca⟩ := ia ht hs
      obtain ⟨hk, ck⟩ := ik (lift_typed (lift_typed ht (X, ⊥)) (Y, ⊥))
        (lift_leaf (lift_leaf hs))
      refine ⟨.let₂ ha hk, ?_⟩
      intro D tail htail rest Ξ θ atomic hθ leaves
      have hw := wk1_typed Y (wk1_typed X htail)
      exact covered_of_eqv (let_let2_eqv ha hk htail)
        (covered_let2_bind profile ha ca (.let₁ hk hw) (ck hw
          (covered_wk1 Y (covered_wk1 X rest)))) atomic hθ leaves

theorem case_raw_written (profile : Profile (α := α) Φ ε)
    (atomic : ∀ i : Fin Γ.length, ∃ x, (Γ.get i).1 = Ty.base x) (h : CaseRaw e Γ A a) :
    ReplyReflection.Written A e Γ a := by
  have typedAndBind : Wf Γ a A e ∧ CoversBind Γ A e a := by
    simpa only [Expr.subst_var] using
      case_raw_coversBind profile h (σ := Expr.var) (fun i => .var i le_rfl) .var
  obtain ⟨typed, accepts⟩ := typedAndBind
  have result : Wf ((A, ⊥) :: Γ) (.var 0 : Expr Φ) A (⊥ : ε) := .var 0 le_rfl
  have resultCovered : Covered ((A, ⊥) :: Γ) A e (.var 0 : Expr Φ) :=
    fun _ ht hs => ReplyReflection.Written.of_leaf (result.subst_typed ht) (hs 0)
  have identity := result.weakenEffect (show (⊥ : ε) ≤ e from bot_le)
  have eta := Eqv.step (.rewrite (.let₁ typed identity) typed (.let1_eta a))
  have cover : Covered Γ A e a := covered_of_eqv eta.symm (accepts identity resultCovered)
  simpa only [Expr.subst_var] using cover (σ := Expr.var) atomic (fun i => .var i le_rfl) .var

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments.Proofs

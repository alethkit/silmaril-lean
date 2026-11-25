module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SequentialEquations
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SeqRenaming

/-! # Sound sequential structural equations -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation

universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} (Ty α) Φ ε)

/-- An inserted zero-use ambient binder contributes no semantic component. -/
theorem denoteSeq_underBinder_zero {n : Nat} {Γ : QCtx (Ty α) n} {e e' : ε}
    {t : Term Φ (n + 1)} {A B C : Ty α}
    (h : HasType .seq (Γ.snoc B) e t C)
    (k : HasType .seq ((Γ.snoc A .zero).snoc B) e' t.underBinder C) :
    denoteSeq M k = denoteSeq M h :=
  Sequential.denote_underBinder_zero M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) h k

/-- Zero-use insertion below two bound components is also semantically inert. -/
theorem denoteSeq_underTwoBinders_zero {n : Nat} {Γ : QCtx (Ty α) n} {e e' : ε}
    {t : Term Φ (n + 2)} {A B C D : Ty α}
    (h : HasType .seq ((Γ.snoc B).snoc C) e t D)
    (k : HasType .seq (((Γ.snoc A .zero).snoc B).snoc C) e' t.underTwoBinders D) :
    denoteSeq M k = denoteSeq M h :=
  Sequential.denote_underTwoBinders_zero M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) h k

set_option backward.isDefEq.respectTransparency false in
/-- Pair elimination factors through ordinary binding of its scrutinee. -/
theorem denoteSeq_pairBind {n : Nat} {Γ Γl Γr : QCtx (Ty α) n}
    {e eL eR : ε} {a : Term Φ n} {c : Term Φ (n + 2)} {A B C : Ty α}
    (s : Γ.Split Γl Γr) (ha : HasType .seq Γr e a (product A B))
    (hc : HasType .seq ((Γl.snoc A).snoc B) e c C)
    (hl : HasType .seq Γ eL (.let₂ a c) C)
    (hr : HasType .seq Γ eR (.let₁ a (.let₂ (.bv 0) c.underTwoBinders)) C) :
    denoteSeq M hl = denoteSeq M hr :=
  Sequential.denote_pairBind M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) s ha hc hl hr

set_option backward.isDefEq.respectTransparency false in
/-- Binding an instruction result agrees with first binding its argument. -/
theorem denoteSeq_letOp {n : Nat} {Γ Γl Γr : QCtx (Ty α) n}
    {e eL eR : ε} {a : Term Φ n} {c : Term Φ (n + 1)} {f : Φ} {C : Ty α}
    (s : Γ.Split Γl Γr) (hf : instrEff f ≤ e)
    (ha : HasType .seq Γr e a (instrSrc f))
    (hc : HasType .seq (Γl.snoc (instrTrg f)) e c C)
    (hl : HasType .seq Γ eL (.let₁ (.op f a) c) C)
    (hr : HasType .seq Γ eR (.let₁ a (.let₁ (.op f (.bv 0)) c.underBinder)) C) :
    denoteSeq M hl = denoteSeq M hr :=
  Sequential.denote_letOp M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) s hf ha hc hl hr

set_option backward.isDefEq.respectTransparency false in
/-- Nested ordinary binding is associative, including the quantitative
reassociation of its three ambient resource groups. -/
theorem denoteSeq_letLet {n : Nat} {Γ Γl Γm Γr Γc : QCtx (Ty α) n}
    {e eL eR : ε} {a : Term Φ n} {b c : Term Φ (n + 1)} {A B C : Ty α}
    (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
    (ha : HasType .seq Γr e a A) (hb : HasType .seq (Γm.snoc A) e b B)
    (hc : HasType .seq (Γl.snoc B) e c C)
    (hl : HasType .seq Γ eL (.let₁ (.let₁ a b) c) C)
    (hr : HasType .seq Γ eR (.let₁ a (.let₁ b c.underBinder)) C) :
    denoteSeq M hl = denoteSeq M hr :=
  Sequential.denote_letLet M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) outer inner ha hb hc hl hr

/-- Returning a just-bound value is the identity continuation, independently
of the particular endpoint typing witnesses. -/
theorem denoteSeq_let_return {n : Nat} {Γ : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {A : Ty α} (ha : HasType .seq Γ e a A)
    (hl : HasType .seq Γ e' (.let₁ a (.bv 0)) A) :
    denoteSeq M hl = denoteSeq M ha :=
  Sequential.denote_let_return M (ControlData.seq M) (denoteSeq_coherent M) ha hl

/-- The unit eta scheme preserves the effectful computation producing unit. -/
theorem denoteSeq_term {n : Nat} {Γ : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} (ha : HasType .seq Γ e a Silmaril.unit)
    (hl : HasType .seq Γ e' (.let₁ a .unit) Silmaril.unit) :
    denoteSeq M hl = denoteSeq M ha :=
  Sequential.denote_term M (ControlData.seq M) (denoteSeq_coherent M) ha hl

end Silmaril.Isotope.Refinement.Models.Denotation

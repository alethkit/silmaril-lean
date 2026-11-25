module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SeqSoundness
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ProductEquations

/-! # Soundness of the sequential product equations -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation

open CategoryTheory
open scoped MonoidalCategory

universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} (Ty α) Φ ε)

/-- The two fresh variables, with an empty ambient context. -/
def pairParametersTyping (A B : Ty α) (e : ε) :
    HasType .seq ((QCtx.nil.snoc A).snoc B) e (.pair (.bv 1) (.bv 0) : Term Φ 2)
      (product A B) :=
  Sequential.pairParametersTyping (F := .seq) A B e

set_option backward.isDefEq.respectTransparency false in
theorem denoteSeq_pairParameters (A B : Ty α) (e : ε) :
    denoteSeq M (pairParametersTyping (Φ := Φ) A B e) =
      M.right (M.leftUnitor A) B :=
  Sequential.denote_pairParameters M (ControlData.seq M) A B e

set_option backward.isDefEq.respectTransparency false in
/-- Pairing the two newest variables discards only the older context. -/
theorem denoteSeq_pairParameters_context {n : Nat} {Γ : QCtx (Ty α) n}
    (hd : Γ.Discardable) {A B : Ty α} {e : ε}
    (k : HasType .seq ((Γ.snoc A).snoc B) e (.pair (.bv 1) (.bv 0) : Term Φ (n + 2))
      (product A B)) :
    denoteSeq M k = M.compose (M.right (M.right (discard M.toSeqData hd) A) B)
      (M.right (M.leftUnitor A) B) :=
  Sequential.denote_pairParameters_context M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) hd k

/-- Pure unit coherence for rebuilding two components. -/
theorem unit_pair_cancel (A B : Ty α) :
    M.compose (M.associatorInv Silmaril.unit A B) (M.right (M.leftUnitor A) B) =
      M.leftUnitor (product A B) :=
  Sequential.unit_pair_cancel M A B

set_option backward.isDefEq.respectTransparency false in
/-- Product eta is valid for an effectful scrutinee and any endpoint derivation. -/
theorem denoteSeq_pairEta {n : Nat} {Γ : QCtx (Ty α) n}
    {e e' : ε} {a : Term Φ n} {A B : Ty α}
    (ha : HasType .seq Γ e a (product A B))
    (hl : HasType .seq Γ e' (.let₂ a (.pair (.bv 1) (.bv 0))) (product A B)) :
    denoteSeq M hl = denoteSeq M ha :=
  Sequential.denote_pairEta M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) ha hl

/-- Associator coherence when a split is followed by two fresh binders. -/
theorem pair_split_pentagon (D E A B : Ty α) :
    M.compose (M.associatorInv (product D E) A B)
      (M.compose (M.right (M.associator D E A) B) (M.associator D (product E A) B)) =
      M.compose (M.associator D E (product A B)) (M.left D (M.associatorInv E A B)) :=
  Sequential.pair_split_pentagon M D E A B

/-- Split an environment before or after unpacking two fresh components. -/
theorem pair_split_bind {X D E A B : Ty α} (f : M.Hom X (product D E)) :
    M.compose (M.associatorInv X A B)
      (M.compose (M.right (M.compose (M.right f A) (M.associator D E A)) B)
        (M.associator D (product E A) B)) =
      M.compose (M.right f (product A B))
        (M.compose (M.associator D E (product A B)) (M.left D (M.associatorInv E A B))) :=
  Sequential.pair_split_bind M f

set_option backward.isDefEq.respectTransparency false in
/-- An ordinary continuation moves through product elimination. -/
theorem denoteSeq_letLetPair {n : Nat} {Γ Γl Γm Γr Γc : QCtx (Ty α) n}
    {e eL eR : ε} {a : Term Φ n} {c : Term Φ (n + 2)} {d : Term Φ (n + 1)}
    {A B C D : Ty α} (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
    (ha : HasType .seq Γr e a (product A B))
    (hc : HasType .seq ((Γm.snoc A).snoc B) e c C)
    (hd : HasType .seq (Γl.snoc C) e d D)
    (hl : HasType .seq Γ eL (.let₁ (.let₂ a c) d) D)
    (hr : HasType .seq Γ eR (.let₂ a (.let₁ c d.underBinder.underBinder)) D) :
    denoteSeq M hl = denoteSeq M hr :=
  Sequential.denote_letLetPair M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) outer inner ha hc hd hl hr

/-- Sequencing the first component through a three-way resource split. The
braiding moves only structural wires, without exchanging the two computations. -/
theorem split_first_pair {n : Nat} {Γ Γr Γl Γa Γb Γrb : QCtx (Ty α) n} {A : Ty α}
    (s : Γ.Split Γr Γl) (t : Γl.Split Γa Γb)
    (u : Γ.Split Γrb Γa) (v : Γrb.Split Γr Γb) (a : M.Hom (packed Γa) A) :
    M.compose (split M.toSeqData u)
      (M.compose (M.left (packed Γrb) a)
        (split M.toSeqData (v.snoc (.left (.used ⊤)) (A := A)))) =
      M.compose (split M.toSeqData s)
        (M.compose (M.left (packed Γr)
          (M.compose (split M.toSeqData t) (M.right a (packed Γb))))
          (M.associatorInv (packed Γr) A (packed Γb))) :=
  Sequential.split_first_pair M s t u v a

/-- Appending an omitted variable does not change sequential interpretation. -/
theorem denoteSeq_lift_zero {n : Nat} {Γ : QCtx (Ty α) n} {e e' : ε}
    {a : Term Φ n} {A B : Ty α} (ha : HasType .seq Γ e a B)
    (hb : HasType .seq (Γ.snoc A .zero) e' a.lift B) :
    denoteSeq M hb = denoteSeq M ha :=
  Sequential.denote_lift_zero M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) ha hb

set_option backward.isDefEq.respectTransparency false in
/-- Product beta preserves the left-to-right evaluation of both components. -/
theorem denoteSeq_pairBeta {n : Nat} {Γ Γl Γr Γa Γb : QCtx (Ty α) n}
    {e eL eR : ε} {a b : Term Φ n} {c : Term Φ (n + 2)} {A B C : Ty α}
    (outer : Γ.Split Γl Γr) (inner : Γl.Split Γa Γb)
    (ha : HasType .seq Γa e a A) (hb : HasType .seq Γb e b B)
    (hc : HasType .seq ((Γr.snoc A).snoc B) e c C)
    (hl : HasType .seq Γ eL (.let₂ (.pair a b) c) C)
    (hr : HasType .seq Γ eR (.let₁ a (.let₁ b.lift c)) C) :
    denoteSeq M hl = denoteSeq M hr :=
  Sequential.denote_pairBeta M (ControlData.seq M) (ControlEnvironment.seq M)
    (denoteSeq_coherent M) outer inner ha hb hc hl hr

/-- Every written sequential equation holds for every endpoint typing witness. -/
theorem denoteSeq_equation {n : Nat} {Γ : QCtx (Ty α) n} {a b : Term Φ n} {A : Ty α}
    {e e' : ε} (h : EquationAxiom (ε := ε) .seq Γ a b A)
    (ha : HasType .seq Γ e a A) (hb : HasType .seq Γ e' b A) :
    denoteSeq M ha = denoteSeq M hb := by
  cases h with
  | letOp s hf harg hc => exact denoteSeq_letOp M s hf harg hc ha hb
  | letLet s t harg hc hd => exact denoteSeq_letLet M s t harg hc hd ha hb
  | letLetPair s t harg hc hd => exact denoteSeq_letLetPair M s t harg hc hd ha hb
  | letCase cap => exact False.elim cap
  | pairBind s harg hc => exact denoteSeq_pairBind M s harg hc ha hb
  | caseBind cap => exact False.elim cap
  | iterBind cap => exact False.elim cap
  | term harg => exact (denoteSeq_term M harg ha).trans (denoteSeq_coherent M harg hb)
  | initial cap => exact False.elim cap
  | pairEta harg => exact (denoteSeq_pairEta M harg ha).trans (denoteSeq_coherent M harg hb)
  | pairBeta s t hleft hright hc => exact denoteSeq_pairBeta M s t hleft hright hc ha hb
  | caseBetaL cap => exact False.elim cap
  | caseBetaR cap => exact False.elim cap
  | caseEta cap => exact False.elim cap
  | fixpoint cap => exact False.elim cap
  | naturality cap => exact False.elim cap
  | codiagonal cap => exact False.elim cap

end Silmaril.Isotope.Refinement.Models.Denotation

module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SequentialEquations
public import Silmaril.Raw.SSA.Isotope.Refinement.Laws

/-! # Product equations shared by every control fragment -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation

open CategoryTheory
open scoped MonoidalCategory

universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (N : ControlEnvironment K) (H : WitnessCoherent M K)

namespace Sequential
include N H

omit N H in
/-- The two fresh variables, with an empty ambient context. -/
def pairParametersTyping (A B : τ) (e : ε) :
    HasType F ((QCtx.nil.snoc A).snoc B) e (.pair (.bv 1) (.bv 0) : Term Φ 2)
      (product A B) := by
  apply HasType.pair ((QCtx.Split.nil.snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
  · apply HasType.var 1
    constructor
    · change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
      exact inf_le_inf bot_le le_rfl
    · intro i hi
      fin_cases i
      · exact le_rfl
      · exact False.elim (hi rfl)
  · exact HasType.var 0 (QCtx.varAllowed_snoc
      (Γ := QCtx.nil.snoc A .zero) (fun i => by fin_cases i; exact le_rfl) B)

omit N H in
set_option backward.isDefEq.respectTransparency false in
theorem denote_pairParameters (A B : τ) (e : ε) :
    denote M.toSeqData K (pairParametersTyping (F := F) (Φ := Φ) A B e) =
      M.right (M.leftUnitor A) B := by
  change M.compose
    (M.compose
      (M.right
        (M.compose (M.right (M.leftUnitorInv Silmaril.unit) A)
          (M.compose (M.associator Silmaril.unit Silmaril.unit A)
            (M.compose (M.left Silmaril.unit (M.braiding Silmaril.unit A))
              (M.associatorInv Silmaril.unit A Silmaril.unit)))) B)
      (M.associator (product Silmaril.unit A) Silmaril.unit B))
    (M.tensor
      (M.compose (M.right (M.discard Silmaril.unit _) A) (M.leftUnitor A))
      (M.compose (M.right (M.discard Silmaril.unit _) B) (M.leftUnitor B))) = _
  rw [M.discard_unit, M.toSeqData.right_identity, M.toSeqData.right_identity,
    M.toSeqData.identity_compose, M.toSeqData.identity_compose]
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let B' : M.toSeqData.PureObject := ⟨B⟩
  let I : M.toSeqData.PureObject := 𝟙_ M.toSeqData.PureObject
  have h : (((λ_ I).inv ▷ A' ≫ (α_ I I A').hom ≫ I ◁ (CategoryTheory.BraidedCategory.braiding I A').hom ≫
      (α_ I A' I).inv) ▷ B' ≫ (α_ (I ⊗ A') I B').hom) ≫
      ((λ_ A').hom ⊗ₘ (λ_ B').hom) = (λ_ A').hom ▷ B' := by
    simp only [I, braiding_tensorUnit_left, Category.assoc]
    monoidal
  exact congrArg Subtype.val h


set_option backward.isDefEq.respectTransparency false in
/-- Pairing the two newest variables discards only the older context. -/
theorem denote_pairParameters_context {n : Nat} {Γ : QCtx τ n}
    (hd : Γ.Discardable) {A B : τ} {e : ε}
    (k : HasType F ((Γ.snoc A).snoc B) e (.pair (.bv 1) (.bv 0) : Term Φ (n + 2))
      (product A B)) :
    denote M.toSeqData K k = M.compose (M.right (M.right (discard M.toSeqData hd) A) B)
      (M.right (M.leftUnitor A) B) := by
  let w := ((QCtx.discardable_iff_weakening_nil.mp hd).up A).up B
  have hn := denote_rename_of_typing M K N H (pairParametersTyping (F := F) (Φ := Φ) A B e) _ w k
  rw [denote_pairParameters] at hn
  have hw : weaken M.toSeqData w = M.right (M.right (discard M.toSeqData hd) A) B := by
    change M.right (M.right (weaken M.toSeqData (QCtx.discardable_iff_weakening_nil.mp hd)) A) B = _
    rw [weaken_nil M (QCtx.discardable_iff_weakening_nil.mp hd)]
  exact hn.trans (congrArg (fun g => M.compose g (M.right (M.leftUnitor A) B)) hw)

omit N H in
/-- Pure unit coherence for rebuilding two components. -/
theorem unit_pair_cancel (A B : τ) :
    M.compose (M.associatorInv Silmaril.unit A B) (M.right (M.leftUnitor A) B) =
      M.leftUnitor (product A B) := by
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let B' : M.toSeqData.PureObject := ⟨B⟩
  have h : (α_ (𝟙_ M.toSeqData.PureObject) A' B').inv ≫ (λ_ A').hom ▷ B' =
      (λ_ (A' ⊗ B')).hom := by monoidal
  exact congrArg Subtype.val h

set_option backward.isDefEq.respectTransparency false in
/-- Product eta is valid for an effectful scrutinee and any endpoint derivation. -/
theorem denote_pairEta {n : Nat} {Γ : QCtx τ n}
    {e e' : ε} {a : Term Φ n} {A B : τ}
    (ha : HasType F Γ e a (product A B))
    (hl : HasType F Γ e' (.let₂ a (.pair (.bv 1) (.bv 0))) (product A B)) :
    denote M.toSeqData K hl = denote M.toSeqData K ha := by
  let w := ((QCtx.discardable_iff_weakening_nil.mp Γ.zero_discardable).up A).up B
  let hp := (pairParametersTyping (F := F) (Φ := Φ) A B e).rename _ w
  have he := H hl (.let₂ (QCtx.Split.zero_left Γ) ha hp)
  apply he.trans
  change M.compose (split M.toSeqData (QCtx.Split.zero_left Γ))
    (M.compose (M.left (packed Γ.zero) (denote M.toSeqData K ha))
      (M.compose (M.associatorInv (packed Γ.zero) A B) (denote M.toSeqData K hp))) = _
  rw [denote_pairParameters_context M K N H Γ.zero_discardable hp,
    ← M.toSeqData.compose_assoc (M.associatorInv _ _ _),
    ← M.toSeqData.associatorInv_natural_left,
    M.toSeqData.compose_assoc, unit_pair_cancel]
  exact zero_context_bind M Γ (denote M.toSeqData K ha) Γ.zero_discardable


omit N H in
/-- Associator coherence when a split is followed by two fresh binders. -/
theorem pair_split_pentagon (D E A B : τ) :
    M.compose (M.associatorInv (product D E) A B)
      (M.compose (M.right (M.associator D E A) B) (M.associator D (product E A) B)) =
      M.compose (M.associator D E (product A B)) (M.left D (M.associatorInv E A B)) := by
  let D' : M.toSeqData.PureObject := ⟨D⟩
  let E' : M.toSeqData.PureObject := ⟨E⟩
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let B' : M.toSeqData.PureObject := ⟨B⟩
  have h : (α_ (D' ⊗ E') A' B').inv ≫ (α_ D' E' A').hom ▷ B' ≫
      (α_ D' (E' ⊗ A') B').hom =
      (α_ D' E' (A' ⊗ B')).hom ≫ D' ◁ (α_ E' A' B').inv := by monoidal
  exact congrArg Subtype.val h

omit N H in
/-- Split an environment before or after unpacking two fresh components. -/
theorem pair_split_bind {X D E A B : τ} (f : M.Hom X (product D E)) :
    M.compose (M.associatorInv X A B)
      (M.compose (M.right (M.compose (M.right f A) (M.associator D E A)) B)
        (M.associator D (product E A) B)) =
      M.compose (M.right f (product A B))
        (M.compose (M.associator D E (product A B)) (M.left D (M.associatorInv E A B))) := by
  rw [M.toSeqData.right_compose]
  simp only [M.toSeqData.compose_assoc]
  rw [← M.toSeqData.compose_assoc (M.associatorInv _ _ _),
    ← M.toSeqData.associatorInv_natural_left, M.toSeqData.compose_assoc,
    pair_split_pentagon]

set_option backward.isDefEq.respectTransparency false in
/-- An ordinary continuation moves through product elimination. -/
theorem denote_letLetPair {n : Nat} {Γ Γl Γm Γr Γc : QCtx τ n}
    {e eL eR : ε} {a : Term Φ n} {c : Term Φ (n + 2)} {d : Term Φ (n + 1)}
    {A B C D : τ} (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
    (ha : HasType F Γr e a (product A B))
    (hc : HasType F ((Γm.snoc A).snoc B) e c C)
    (hd : HasType F (Γl.snoc C) e d D)
    (hl : HasType F Γ eL (.let₁ (.let₂ a c) d) D)
    (hr : HasType F Γ eR (.let₂ a (.let₁ c d.underBinder.underBinder)) D) :
    denote M.toSeqData K hl = denote M.toSeqData K hr := by
  obtain ⟨Γmr, u, v⟩ := outer.swapAssoc inner.symm
  let kd1 := hd.rename _ ((QCtx.Weakening.insertZero Γl A).up C)
  let kd := kd1.rename _ ((QCtx.Weakening.insertZero (Γl.snoc A .zero) B).up C)
  let si := (inner.snoc (.right (.used ⊤)) (A := A)).snoc (.right (.used ⊤)) (A := B)
  let ki := HasType.let₁ si hc kd
  have hkd : denote M.toSeqData K kd = denote M.toSeqData K hd :=
    (denote_underBinder_zero M K N H kd1 kd).trans (denote_underBinder_zero M K N H hd kd1)
  have hi : M.compose (M.associatorInv (packed Γc) A B) (denote M.toSeqData K ki) =
      M.compose (M.right (split M.toSeqData inner) (product A B))
        (M.compose (M.associator (packed Γl) (packed Γm) (product A B))
          (M.compose (M.left (packed Γl)
            (M.compose (M.associatorInv (packed Γm) A B) (denote M.toSeqData K hc)))
            (denote M.toSeqData K hd))) := by
    change M.compose (M.associatorInv (packed Γc) A B)
      (M.compose
        (M.compose (M.right
          (M.compose (M.right (split M.toSeqData inner) A)
            (M.associator (packed Γl) (packed Γm) A)) B)
          (M.associator (packed Γl) (product (packed Γm) A) B))
        (M.compose (M.left (packed Γl) (denote M.toSeqData K hc)) (denote M.toSeqData K kd))) = _
    rw [hkd, ← M.toSeqData.compose_assoc, pair_split_bind]
    simp only [M.toSeqData.compose_assoc, M.toSeqData.left_compose]
  calc
    denote M.toSeqData K hl = denote M.toSeqData K (.let₁ u.symm (.let₂ v ha hc) hd) := H _ _
    _ = denote M.toSeqData K (.let₂ outer ha ki) := by
      change M.compose (split M.toSeqData u.symm)
          (M.compose (M.left (packed Γl)
            (M.compose (split M.toSeqData v)
              (M.compose (M.left (packed Γm) (denote M.toSeqData K ha))
                (M.compose (M.associatorInv (packed Γm) A B) (denote M.toSeqData K hc)))))
            (denote M.toSeqData K hd)) =
        M.compose (split M.toSeqData outer)
          (M.compose (M.left (packed Γc) (denote M.toSeqData K ha))
            (M.compose (M.associatorInv (packed Γc) A B) (denote M.toSeqData K ki)))
      rw [hi, ← M.toSeqData.compose_assoc,
        split_bind_assoc M outer inner u.symm v]
      simp only [M.toSeqData.compose_assoc]
    _ = denote M.toSeqData K hr := H _ _


omit N H in
/-- Sequencing the first component through a three-way resource split. The
braiding moves only structural wires, without exchanging the two computations. -/
theorem split_first_pair {n : Nat} {Γ Γr Γl Γa Γb Γrb : QCtx τ n} {A : τ}
    (s : Γ.Split Γr Γl) (t : Γl.Split Γa Γb)
    (u : Γ.Split Γrb Γa) (v : Γrb.Split Γr Γb) (a : M.Hom (packed Γa) A) :
    M.compose (split M.toSeqData u)
      (M.compose (M.left (packed Γrb) a)
        (split M.toSeqData (v.snoc (.left (.used ⊤)) (A := A)))) =
      M.compose (split M.toSeqData s)
        (M.compose (M.left (packed Γr)
          (M.compose (split M.toSeqData t) (M.right a (packed Γb))))
          (M.associatorInv (packed Γr) A (packed Γb))) := by
  change M.compose (split M.toSeqData u)
    (M.compose (M.left (packed Γrb) a)
      (M.compose (M.right (split M.toSeqData v) A)
        (M.compose (M.associator (packed Γr) (packed Γb) A)
          (M.compose (M.left (packed Γr) (M.braiding (packed Γb) A))
            (M.associatorInv (packed Γr) A (packed Γb)))))) = _
  rw [← M.toSeqData.compose_assoc (M.left (packed Γrb) a),
    ← M.toSeqData.exchange_left_pure _ a (split_pure M.toSeqData v)]
  simp only [M.toSeqData.compose_assoc]
  rw [← M.toSeqData.compose_assoc (M.left (product (packed Γr) (packed Γb)) a),
    ← M.toSeqData.associator_natural_right]
  simp only [M.toSeqData.compose_assoc]
  rw [← M.toSeqData.compose_assoc (M.left (packed Γr) (M.left (packed Γb) a)),
    ← M.toSeqData.left_compose, M.toSeqData.braiding_natural_right, M.toSeqData.left_compose]
  rw [← M.toSeqData.compose_assoc (split M.toSeqData u),
    ← M.toSeqData.compose_assoc (M.compose (split M.toSeqData u) _),
    M.toSeqData.compose_assoc (split M.toSeqData u), split_assoc M.toSeqData u v s t.symm]
  simp only [M.toSeqData.compose_assoc]
  rw [← M.toSeqData.compose_assoc (M.left (packed Γr) (split M.toSeqData t.symm)),
    ← M.toSeqData.left_compose, split_symm M.toSeqData t.symm]
  simp only [M.toSeqData.left_compose, M.toSeqData.compose_assoc]

/-- Appending an omitted variable does not change sequential interpretation. -/
theorem denote_lift_zero {n : Nat} {Γ : QCtx τ n} {e e' : ε}
    {a : Term Φ n} {A B : τ} (ha : HasType F Γ e a B)
    (hb : HasType F (Γ.snoc A .zero) e' a.lift B) :
    denote M.toSeqData K hb = denote M.toSeqData K ha := by
  have hn := denote_rename_of_typing M K N H ha Fin.succ (QCtx.Weakening.insertZero Γ A) hb
  have hw : weaken M.toSeqData (QCtx.Weakening.insertZero Γ A) = M.identity (packed Γ) :=
    (congrArg Subtype.val (weakenPure_skip M (QCtx.Weakening.refl Γ)
      (A := A) (q := .zero) le_rfl)).trans (weaken_refl M.toSeqData Γ)
  exact hn.trans (by rw [hw]; exact M.toSeqData.identity_compose _)


set_option backward.isDefEq.respectTransparency false in
/-- Product beta preserves the left-to-right evaluation of both components. -/
theorem denote_pairBeta {n : Nat} {Γ Γl Γr Γa Γb : QCtx τ n}
    {e eL eR : ε} {a b : Term Φ n} {c : Term Φ (n + 2)} {A B C : τ}
    (outer : Γ.Split Γl Γr) (inner : Γl.Split Γa Γb)
    (ha : HasType F Γa e a A) (hb : HasType F Γb e b B)
    (hc : HasType F ((Γr.snoc A).snoc B) e c C)
    (hl : HasType F Γ eL (.let₂ (.pair a b) c) C)
    (hr : HasType F Γ eR (.let₁ a (.let₁ b.lift c)) C) :
    denote M.toSeqData K hl = denote M.toSeqData K hr := by
  obtain ⟨Γbr, u, v⟩ := outer.swapAssoc inner.symm
  let kb := hb.rename Fin.succ (QCtx.Weakening.insertZero Γb A)
  let si := v.symm.snoc (.left (.used ⊤)) (A := A)
  let ki := HasType.let₁ si kb hc
  have hkb : denote M.toSeqData K kb = denote M.toSeqData K hb := denote_lift_zero M K N H hb kb
  have he : denote M.toSeqData K (.let₁ u ha ki) = denote M.toSeqData K (.let₂ outer.symm (.pair inner ha hb) hc) := by
    change M.compose (split M.toSeqData u)
        (M.compose (M.left (packed Γbr) (denote M.toSeqData K ha))
          (M.compose (split M.toSeqData si)
            (M.compose (M.left (product (packed Γr) A) (denote M.toSeqData K kb)) (denote M.toSeqData K hc)))) =
      M.compose (split M.toSeqData outer.symm)
        (M.compose (M.left (packed Γr)
          (M.compose (split M.toSeqData inner) (M.tensor (denote M.toSeqData K ha) (denote M.toSeqData K hb))))
          (M.compose (M.associatorInv (packed Γr) A B) (denote M.toSeqData K hc)))
    rw [hkb, ← M.toSeqData.compose_assoc (M.left (packed Γbr) _),
      ← M.toSeqData.compose_assoc (split M.toSeqData u)]
    rw [split_first_pair M outer.symm inner u v.symm]
    simp only [SeqData.tensor, M.toSeqData.left_compose, M.toSeqData.compose_assoc]
    rw [← M.toSeqData.compose_assoc (M.left (packed Γr) (M.left A (denote M.toSeqData K hb))),
      M.toSeqData.associatorInv_natural_right]
    simp only [M.toSeqData.compose_assoc]
  exact (H hl (.let₂ outer.symm (.pair inner ha hb) hc)).trans
    (he.symm.trans (H (.let₁ u ha ki) hr))

end Sequential
end Silmaril.Isotope.Refinement.Models.Denotation

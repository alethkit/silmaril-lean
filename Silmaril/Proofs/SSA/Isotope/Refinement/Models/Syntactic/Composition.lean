module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Basic

/-! # Sequential composition of written syntactic arrows -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {A B C : τ}

/-- Insert an unused input slot behind the single parameter of a continuation. -/
def continuation (a : Term Φ 1) : Term Φ 2 := Tm.rename (Tm.up (Fin.succ : Fin 0 → Fin 1)) a

def composeTerm (a b : Term Φ 1) : Term Φ 1 := .let₁ a (continuation b)

/-- All the original input is assigned to the first computation. -/
theorem inputSplit (A : τ) : (input A).Split (QCtx.nil.snoc A .zero) (input A) :=
  QCtx.Split.snoc QCtx.Split.nil (.right _)

/-- Sequencing uses a zero-annotated old input in the continuation's context. -/
def composeDeriv {e : ε} {a b : Term Φ 1}
    (ha : HasType F (input A) e a B) (hb : HasType F (input B) e b C) :
    HasType F (input A) e (composeTerm a b) C :=
  .let₁ (inputSplit A) ha
    (hb.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up B))

/-- Raw, well-typed composition before quotienting by equations. -/
def composeArrow (a : Arrow (Φ := Φ) (ε := ε) F A B) (b : Arrow (Φ := Φ) (ε := ε) F B C) :
    Arrow (Φ := Φ) (ε := ε) F A C :=
  ⟨composeTerm a.val b.val, by
    obtain ⟨da⟩ := a.property
    obtain ⟨db⟩ := b.property
    exact ⟨composeDeriv da db⟩⟩

theorem input_linearity (A : τ) : (input A).linearity = quantity A := by
  simp only [input, QCtx.linearity_snoc, Usage.linearity_used, inf_top_eq, QCtx.linearity_nil]

/-- A continuation variable can ignore the zero-annotated old input. -/
def parameterDeriv (A B : τ) (q : Usage) (e : ε)
    (h : Usage.effective (.used .linear) (quantity B) ≤ Usage.effective q (quantity B)) :
    HasType F ((QCtx.nil.snoc A .zero).snoc B q) e (.bv 0 : Term Φ 2) B := by
  apply HasType.var (i := 0)
  constructor
  · exact h
  · intro j hj
    refine Fin.cases (fun h => False.elim (h rfl)) (fun i _ => ?_) j hj
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact le_rfl

/-- The right identity equation uses linear beta, so the computation may have any effect. -/
theorem compose_identity_equates (R : Relation τ Φ)
    (a : Arrow (Φ := Φ) (ε := ε) F A B) :
    Equates (ε := ε) F R (input A) (composeArrow a (identityArrow B)).val a.val B := by
  obtain ⟨da⟩ := a.property
  have law (p : Polarity) : DirectionalAxiom (ε := ε) F p (input A)
      (.let₁ a.val (.bv 0)) a.val B := by
    simpa only [Tm.instantiate, Tm.bsubst, Fin.cases_zero] using
      (DirectionalAxiom.beta (p := p) (inputSplit A).symm da
        (parameterDeriv A B (.used .linear) (⊥ : ε) le_rfl)
        (parameterDeriv A B (.used ⊤) (⊥ : ε)
          (by simp only [Usage.effective, Usage.used_mul_used, Usage.used_le_used, top_inf_eq]; exact inf_le_right))
        (EffectSystem.moves_pure p ⊤)
        (show Usage.used .linear ≤ Usage.used ((input A).linearity ⊓ EffectSystem.quantity p ⊤)
          from (Usage.used_le_used _ _).2 bot_le))
  exact ⟨.directional .positive (law _) (composeArrow a (identityArrow B)).property a.property,
    .directional .negative (law _) (composeArrow a (identityArrow B)).property a.property⟩

@[simp] theorem instantiate_continuation (b : Term Φ 1) :
    Tm.instantiate (continuation b) (.bv 0) = b := by
  rw [Tm.instantiate, continuation, Tm.bsubst_rename]
  calc
    Tm.bsubst _ b = Tm.bsubst Tm.bv b := by
      apply Tm.bsubst_congr
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
    _ = b := Tm.bsubst_id b

/-- The original parameter's type quantity is sufficient for its own continuation. -/
def continuationDeriv {e : ε} {b : Term Φ 1} (db : HasType F (input A) e b B) :
    HasType F ((QCtx.nil.snoc A .zero).snoc A (.used (quantity A))) e (continuation b) B :=
  db.rename _ (.cons (QCtx.Weakening.insertZero QCtx.nil A)
    (by simp only [Usage.effective, Usage.used_mul_used, top_inf_eq, inf_idem]; exact le_rfl))

/-- Left identity is pure beta after restricting the parameter's annotation to
its intrinsic type quantity; no duplicability of linear inputs is assumed. -/
theorem identity_compose_equates (R : Relation τ Φ)
    (b : Arrow (Φ := Φ) (ε := ε) F A B) :
    Equates (ε := ε) F R (input A) (composeArrow (identityArrow A) b).val b.val B := by
  obtain ⟨db⟩ := b.property
  have law (p : Polarity) : DirectionalAxiom (ε := ε) F p (input A)
      (.let₁ (.bv 0) (continuation b.val)) b.val B := by
    simpa only [instantiate_continuation] using
      (DirectionalAxiom.beta (p := p) (inputSplit A).symm (identityDeriv A (⊥ : ε))
        (continuationDeriv db)
        (db.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up A))
        (EffectSystem.pure_moves p ⊤)
        (by simp only [input_linearity, EffectSystem.quantity_pure, inf_top_eq]; exact le_rfl))
  exact ⟨.directional .positive (law _) (composeArrow (identityArrow A) b).property b.property,
    .directional .negative (law _) (composeArrow (identityArrow A) b).property b.property⟩

/-- Renaming a singleton continuation under two binders is insensitive to the
unused older input. This is the raw associativity calculation. -/
theorem continuation_compose (a b : Term Φ 1) :
    continuation (composeTerm a b) = .let₁ (continuation a) (continuation b).underBinder := by
  simp only [continuation, composeTerm, Tm.rename, Tm.underBinder, Tm.rename_comp]
  congr 1
  apply Tm.rename_congr
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

/-- Associativity is the written let-reassociation axiom at the quantitative split. -/
theorem compose_assoc_equates (R : Relation τ Φ)
    {D : τ} (a : Arrow (Φ := Φ) (ε := ε) F A B)
    (b : Arrow (Φ := Φ) (ε := ε) F B C) (c : Arrow (Φ := Φ) (ε := ε) F C D) :
    Equates (ε := ε) F R (input A) (composeArrow (composeArrow a b) c).val
      (composeArrow a (composeArrow b c)).val D := by
  obtain ⟨da⟩ := a.property
  obtain ⟨db⟩ := b.property
  obtain ⟨dc⟩ := c.property
  apply Equates.ofAxiom _ (composeArrow (composeArrow a b) c).property
    (composeArrow a (composeArrow b c)).property
  change EquationAxiom (ε := ε) F (input A)
    (.let₁ (.let₁ a.val (continuation b.val)) (continuation c.val))
    (.let₁ a.val (continuation (composeTerm b.val c.val))) D
  rw [continuation_compose]
  exact
    (EquationAxiom.letLet (inputSplit A)
      (QCtx.Split.snoc QCtx.Split.nil (.left .zero)) da
      (db.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up B))
      (dc.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up C)))

end Silmaril.Isotope.Refinement.Models.Syntactic

module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Composition

/-! # The primitive and tensor operations on syntactic arrows -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {A B C : τ}

/-- An instruction receives the single input value. -/
def instructionDeriv (f : Φ) :
    HasType F (input (instrSrc f : τ)) (instrEff f : ε) (.op f (.bv 0) : Term Φ 1) (instrTrg f) :=
  .op le_rfl (identityDeriv _ _)

def instructionArrow (f : Φ) : Arrow (Φ := Φ) (ε := ε) F (instrSrc f : τ) (instrTrg f : τ) :=
  ⟨.op f (.bv 0), ⟨(instructionDeriv f).top⟩⟩

/-- All three slots remain in scope; only the pair components are used. -/
def pairContext (P A B : τ) : QCtx τ 3 := ((QCtx.nil.snoc P .zero).snoc A).snoc B

def pairLeftContext (P A B : τ) : QCtx τ 3 := ((QCtx.nil.snoc P .zero).snoc A).snoc B .zero

def pairRightContext (P A B : τ) : QCtx τ 3 := ((QCtx.nil.snoc P .zero).snoc A .zero).snoc B

/-- The two components of a pair are assigned independently, without duplication. -/
theorem pairSplit (P A B : τ) :
    (pairContext P A B).Split (pairLeftContext P A B) (pairRightContext P A B) :=
  ((QCtx.Split.nil.snoc (.left .zero)).snoc (.left (.used ⊤))).snoc (.right (.used ⊤))

/-- Variable zero in a context with only zero-usage older slots. -/
def rightParameter (P A B : τ) (e : ε) :
    HasType F (pairRightContext P A B) e (.bv 0 : Term Φ 3) B := by
  apply HasType.var (i := 0)
  constructor
  · change Usage.used (.linear ⊓ quantity B) ≤ Usage.used (⊤ ⊓ quantity B)
    exact (Usage.used_le_used _ _).2 (inf_le_right.trans_eq (top_inf_eq _).symm)
  · intro i hi
    refine Fin.cases (fun h => False.elim (h rfl)) (fun j _ => ?_) i hi
    refine Fin.cases ?_ (fun k => ?_) j
    · exact le_rfl
    · have hk : k = 0 := Fin.eq_zero k
      subst k
      exact le_rfl

/-- Variable one with zero-usage slots on both sides. -/
def leftParameter (P A B : τ) (e : ε) :
    HasType F (pairLeftContext P A B) e (.bv 1 : Term Φ 3) A := by
  apply HasType.var (i := 1)
  constructor
  · change Usage.used (.linear ⊓ quantity A) ≤ Usage.used (⊤ ⊓ quantity A)
    exact (Usage.used_le_used _ _).2 (inf_le_right.trans_eq (top_inf_eq _).symm)
  · intro i hi
    refine Fin.cases (fun _ => le_rfl) (fun j hj => ?_) i hi
    refine Fin.cases (fun h => False.elim (h rfl)) (fun k _ => ?_) j hj
    have hk : k = 0 := Fin.eq_zero k
    subst k
    exact le_rfl

/-- Embed a single-input computation on the right component of a pair. -/
def onRight (a : Term Φ 1) : Term Φ 3 :=
  Tm.rename (Tm.up (fun i : Fin 0 => i.succ.succ)) a

/-- Embed a single-input computation on the left component of a pair. -/
def onLeft (a : Term Φ 1) : Term Φ 3 :=
  Tm.rename (fun i => (Tm.up (Fin.succ : Fin 0 → Fin 1) i).succ) a

def leftTerm (a : Term Φ 1) : Term Φ 1 := .let₂ (.bv 0) (.pair (.bv 1) (onRight a))

def rightTerm (a : Term Φ 1) : Term Φ 1 := .let₂ (.bv 0) (.pair (onLeft a) (.bv 0))

/-- Tensoring on the left preserves the computation's effect. -/
def leftDeriv (A : τ) {e : ε} {a : Term Φ 1} (da : HasType F (input B) e a C) :
    HasType F (input (product A B)) e (leftTerm a) (product A C) := by
  apply HasType.let₂ (inputSplit (product A B)) (identityDeriv _ _)
  apply HasType.pair (pairSplit (product A B) A B) (leftParameter _ _ _ _)
  exact da.rename _ (.cons (.skip (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl)

/-- Tensoring on the right preserves the computation's effect. -/
def rightDeriv (C : τ) {e : ε} {a : Term Φ 1} (da : HasType F (input A) e a B) :
    HasType F (input (product A C)) e (rightTerm a) (product B C) := by
  apply HasType.let₂ (inputSplit (product A C)) (identityDeriv _ _)
  apply HasType.pair (pairSplit (product A C) A C) _ (rightParameter _ _ _ _)
  exact da.rename _ (.skip (.cons (.skip (.refl QCtx.nil) le_rfl) le_rfl) le_rfl)

def leftArrow (A : τ) (a : Arrow (Φ := Φ) (ε := ε) F B C) :
    Arrow (Φ := Φ) (ε := ε) F (product A B) (product A C) :=
  ⟨leftTerm a.val, by obtain ⟨da⟩ := a.property; exact ⟨leftDeriv A da⟩⟩

def rightArrow (a : Arrow (Φ := Φ) (ε := ε) F A B) (C : τ) :
    Arrow (Φ := Φ) (ε := ε) F (product A C) (product B C) :=
  ⟨rightTerm a.val, by obtain ⟨da⟩ := a.property; exact ⟨rightDeriv C da⟩⟩

/-- Discard is available precisely for affine types. -/
def discardDeriv (A : τ) (hA : Quantity.affine ≤ quantity A) (e : ε) :
    HasType F (input A) e (.unit : Term Φ 1) Silmaril.unit := by
  apply HasType.unit
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simpa only [input, QCtx.effective, QCtx.snoc_zero, Usage.effective, Usage.used_mul_used,
    top_inf_eq, Usage.zero_le_used] using hA

/-- Copy is available precisely for relevant types. -/
def copyDeriv (A : τ) (hA : Quantity.relevant ≤ quantity A) (e : ε) :
    HasType F (input A) e (.pair (.bv 0) (.bv 0) : Term Φ 1) (product A A) :=
  .pair (QCtx.Split.nil.snoc (.both (.used ⊤) (by
    simpa only [Usage.effective, Usage.used_mul_used, top_inf_eq, Usage.used_le_used] using hA)))
    (identityDeriv A e) (identityDeriv A e)

def discardArrow (A : τ) (hA : Quantity.affine ≤ quantity A) :
    Arrow (Φ := Φ) (ε := ε) F A Silmaril.unit := ⟨.unit, ⟨discardDeriv A hA ⊤⟩⟩

def copyArrow (A : τ) (hA : Quantity.relevant ≤ quantity A) :
    Arrow (Φ := Φ) (ε := ε) F A (product A A) :=
  ⟨.pair (.bv 0) (.bv 0), ⟨copyDeriv A hA ⊤⟩⟩

/-- The pure injections use the exact fragment's case capability. -/
def inlDeriv (cap : F.HasCase) (A B : τ) (e : ε) :
    HasType F (input A) e (.inl (.bv 0) : Term Φ 1) (coprod A B) :=
  .inl cap (identityDeriv A e)

def inrDeriv (cap : F.HasCase) (A B : τ) (e : ε) :
    HasType F (input B) e (.inr (.bv 0) : Term Φ 1) (coprod A B) :=
  .inr cap (identityDeriv B e)

def abortDeriv (cap : F.HasCase) (A : τ) (e : ε) :
    HasType F (input Silmaril.empty) e (.abort (.bv 0) : Term Φ 1) A :=
  .abort cap (identityDeriv Silmaril.empty e)

def inlArrow (cap : F.HasCase) (A B : τ) : Arrow (Φ := Φ) (ε := ε) F A (coprod A B) :=
  ⟨.inl (.bv 0), ⟨inlDeriv cap A B ⊤⟩⟩

def inrArrow (cap : F.HasCase) (A B : τ) : Arrow (Φ := Φ) (ε := ε) F B (coprod A B) :=
  ⟨.inr (.bv 0), ⟨inrDeriv cap A B ⊤⟩⟩

def abortArrow (cap : F.HasCase) (A : τ) : Arrow (Φ := Φ) (ε := ε) F Silmaril.empty A :=
  ⟨.abort (.bv 0), ⟨abortDeriv cap A ⊤⟩⟩

def descTerm (a b : Term Φ 1) : Term Φ 1 := .case (.bv 0) (continuation a) (continuation b)

def descDeriv (cap : F.HasCase) {e : ε} {a b : Term Φ 1}
    (da : HasType F (input A) e a C) (db : HasType F (input B) e b C) :
    HasType F (input (coprod A B)) e (descTerm a b) C :=
  .case cap (inputSplit _) (identityDeriv _ _)
    (da.rename _ ((QCtx.Weakening.insertZero QCtx.nil (coprod A B)).up A))
    (db.rename _ ((QCtx.Weakening.insertZero QCtx.nil (coprod A B)).up B))

def descArrow (cap : F.HasCase) (a : Arrow (Φ := Φ) (ε := ε) F A C)
    (b : Arrow (Φ := Φ) (ε := ε) F B C) : Arrow (Φ := Φ) (ε := ε) F (coprod A B) C :=
  ⟨descTerm a.val b.val, by
    obtain ⟨da⟩ := a.property
    obtain ⟨db⟩ := b.property
    exact ⟨descDeriv cap da db⟩⟩

/-- A zero-usage old input imposes no restriction on an iterative body. -/
theorem zeroInput_linearity (A : τ) : (QCtx.nil.snoc A .zero).linearity = ⊤ := by
  simp only [QCtx.linearity_snoc, Usage.linearity_zero, QCtx.linearity_nil, inf_top_eq]
  rfl

def iterateTerm (a : Term Φ 1) : Term Φ 1 := .iter (.bv 0) (continuation a)

def iterateDeriv (cap : F.HasIter) {e : ε} (iterable : EffectSystem.iterable e)
    {a : Term Φ 1} (da : HasType F (input A) e a (coprod B A)) :
    HasType F (input A) e (iterateTerm a) B :=
  .iter cap (inputSplit A) (zeroInput_linearity A) iterable (identityDeriv _ _)
    (da.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up A))

def iterateArrow (cap : F.HasIter) (a : Arrow (Φ := Φ) (ε := ε) F A (coprod B A)) :
    Arrow (Φ := Φ) (ε := ε) F A B :=
  ⟨iterateTerm a.val, by
    obtain ⟨da⟩ := a.property
    exact ⟨iterateDeriv cap EffectSystem.iterable_top da⟩⟩

end Silmaril.Isotope.Refinement.Models.Syntactic

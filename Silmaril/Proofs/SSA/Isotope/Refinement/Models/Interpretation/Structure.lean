module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Basic
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Associator
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ProductEquations

/-! # Interpretation of the native structural representatives

These are categorical computations on the actual typing derivations; no
soundness assumption on the quotient relation is used.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment} (K : ControlData M.toSeqData F)

/-- Removing the singleton padding before unpacking a product leaves one associator. -/
theorem denoteArrow_unpack {A B C : τ} {e : ε} {t : Term Φ 3}
    (h : HasType F (Syntactic.pairContext (product A B) A B) e t C) :
    denoteArrow M.toSeqData K (.let₂ (Syntactic.inputSplit (product A B)) (Syntactic.identityDeriv _ e) h) =
      M.compose (M.leftUnitorInv (product A B))
        (M.compose (M.associatorInv Silmaril.unit A B) (Denotation.denote M.toSeqData K h)) := by
  change M.compose (M.leftUnitorInv (product A B))
    (M.compose (split M.toSeqData (Syntactic.inputSplit (product A B)))
      (M.compose (M.left Silmaril.unit
        (M.compose (M.right (discard M.toSeqData (fun i : Fin 0 => Fin.elim0 i)) (product A B))
          (M.leftUnitor (product A B))))
        (M.compose (M.associatorInv Silmaril.unit A B) (Denotation.denote M.toSeqData K h)))) = _
  have hp : M.compose (split M.toSeqData (Syntactic.inputSplit (product A B)))
      (M.left Silmaril.unit
        (M.compose (M.right (discard M.toSeqData (Γ := QCtx.nil) (fun i => Fin.elim0 i)) (product A B))
          (M.leftUnitor (product A B)))) = M.identity (product Silmaril.unit (product A B)) :=
    newest_split_variable M QCtx.nil (product A B) (fun i => Fin.elim0 i)
  rw [← M.toSeqData.compose_assoc (split M.toSeqData _)]
  exact congrArg (M.compose (M.leftUnitorInv (product A B)))
    ((congrArg (fun f => M.compose f (M.compose (M.associatorInv Silmaril.unit A B)
      (Denotation.denote M.toSeqData K h))) hp).trans (M.toSeqData.identity_compose _))

/-- The syntactic inverse left unitor inserts exactly the semantic unit. -/
theorem denoteArrow_leftUnitInvDeriv (A : τ) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.leftUnitInvDeriv (F := F) A e) = M.leftUnitorInv A := by
  change M.compose (M.leftUnitorInv A)
    (M.compose (M.compose (M.right (M.leftUnitorInv Silmaril.unit) A)
      (M.associator Silmaril.unit Silmaril.unit A))
      (M.tensor (M.discard Silmaril.unit _)
        (M.compose (M.right (M.discard Silmaril.unit _) A) (M.leftUnitor A)))) = _
  rw [M.discard_unit, M.toSeqData.right_identity, M.toSeqData.identity_compose]
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let I : M.toSeqData.PureObject := 𝟙_ M.toSeqData.PureObject
  have h : (λ_ A').inv ≫ ((λ_ I).inv ▷ A' ≫ (α_ I I A').hom) ≫ (𝟙 I ⊗ₘ (λ_ A').hom) =
      (λ_ A').inv := by monoidal
  exact congrArg Subtype.val h

/-- The syntactic inverse right unitor inserts exactly the semantic unit. -/
theorem denoteArrow_rightUnitInvDeriv (A : τ) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.rightUnitInvDeriv (F := F) A e) = M.rightUnitorInv A := by
  change M.compose (M.leftUnitorInv A)
    (M.compose (M.compose (M.right (M.leftUnitorInv Silmaril.unit) A)
      (M.compose (M.associator Silmaril.unit Silmaril.unit A)
        (M.compose (M.left Silmaril.unit (M.braiding Silmaril.unit A))
          (M.associatorInv Silmaril.unit A Silmaril.unit))))
      (M.tensor (M.compose (M.right (M.discard Silmaril.unit _) A) (M.leftUnitor A))
        (M.discard Silmaril.unit _))) = _
  rw [M.discard_unit, M.toSeqData.right_identity, M.toSeqData.identity_compose]
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let I : M.toSeqData.PureObject := 𝟙_ M.toSeqData.PureObject
  have h : (λ_ A').inv ≫ ((λ_ I).inv ▷ A' ≫ (α_ I I A').hom ≫
      I ◁ (CategoryTheory.BraidedCategory.braiding I A').hom ≫ (α_ I A' I).inv) ≫ ((λ_ A').hom ⊗ₘ 𝟙 I) = (ρ_ A').inv := by
    simp only [I, braiding_tensorUnit_left]
    monoidal
  exact congrArg Subtype.val h

/-- The native left-unitor representative has the chosen categorical interpretation. -/
theorem denoteArrow_leftUnitDeriv (A : τ) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.leftUnitDeriv (F := F) A e) = M.leftUnitor A := by
  change denoteArrow M.toSeqData K
    (.let₂ (Syntactic.inputSplit _) (Syntactic.identityDeriv _ e) (Syntactic.leftUnitBodyDeriv _ A e)) = _
  rw [denoteArrow_unpack]
  change M.compose (M.leftUnitorInv (product Silmaril.unit A))
    (M.compose (M.associatorInv Silmaril.unit Silmaril.unit A)
      (M.compose (M.right (M.discard (product Silmaril.unit Silmaril.unit) _) A) (M.leftUnitor A))) = _
  have hd (h : Quantity.affine ≤ quantity (product (Silmaril.unit : τ) Silmaril.unit)) :
      M.discard (product Silmaril.unit Silmaril.unit) h = M.leftUnitor Silmaril.unit :=
    (M.pure_to_unit_unique _ (M.toSeqData.leftUnitor_pure Silmaril.unit) h).symm
  rw [hd]
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let I : M.toSeqData.PureObject := 𝟙_ M.toSeqData.PureObject
  have h : (λ_ (I ⊗ A')).inv ≫ (α_ I I A').inv ≫ (λ_ I).hom ▷ A' ≫ (λ_ A').hom =
      (λ_ A').hom := by monoidal
  exact congrArg Subtype.val h

/-- The native right-unitor representative has the chosen categorical interpretation. -/
theorem denoteArrow_rightUnitDeriv (A : τ) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.rightUnitDeriv (F := F) A e) = M.rightUnitor A := by
  change denoteArrow M.toSeqData K
    (.let₂ (Syntactic.inputSplit _) (Syntactic.identityDeriv _ e) (Syntactic.rightUnitBodyDeriv _ A e)) = _
  rw [denoteArrow_unpack]
  change M.compose (M.leftUnitorInv (product A Silmaril.unit))
    (M.compose (M.associatorInv Silmaril.unit A Silmaril.unit)
      (M.compose (M.right (M.compose (M.right (M.discard Silmaril.unit _) A) (M.leftUnitor A)) Silmaril.unit)
        (M.compose (M.left A (M.discard Silmaril.unit _)) (M.rightUnitor A)))) = _
  rw [M.discard_unit, M.toSeqData.right_identity, M.toSeqData.identity_compose,
    M.toSeqData.left_identity, M.toSeqData.identity_compose]
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let I : M.toSeqData.PureObject := 𝟙_ M.toSeqData.PureObject
  have h : (λ_ (A' ⊗ I)).inv ≫ (α_ I A' I).inv ≫ (λ_ A').hom ▷ I ≫ (ρ_ A').hom =
      (ρ_ A').hom := by monoidal
  exact congrArg Subtype.val h

/-- A selected left parameter ignores only zero-annotated slots. -/
theorem denote_leftParameter (P A B : τ) (e : ε) :
    Denotation.denote M.toSeqData K (Syntactic.leftParameter (F := F) P A B e) = M.leftUnitor A := by
  change M.compose (M.right (M.discard Silmaril.unit _) A) (M.leftUnitor A) = _
  rw [M.discard_unit, M.toSeqData.right_identity, M.toSeqData.identity_compose]

/-- A selected right parameter ignores only zero-annotated slots. -/
theorem denote_rightParameter (P A B : τ) (e : ε) :
    Denotation.denote M.toSeqData K (Syntactic.rightParameter (F := F) P A B e) = M.leftUnitor B := by
  change M.compose (M.right (M.discard Silmaril.unit _) B) (M.leftUnitor B) = _
  rw [M.discard_unit, M.toSeqData.right_identity, M.toSeqData.identity_compose]

/-- The native symmetry representative denotes the chosen categorical braiding. -/
theorem denoteArrow_swapDeriv (A B : τ) (e : ε) :
    denoteArrow M.toSeqData K (Syntactic.swapDeriv (F := F) A B e) = M.braiding A B := by
  change denoteArrow M.toSeqData K
    (.let₂ (Syntactic.inputSplit _) (Syntactic.identityDeriv _ e)
      (.pair (Syntactic.pairSplit (product A B) A B).symm
        (Syntactic.rightParameter _ _ _ e) (Syntactic.leftParameter _ _ _ e))) = _
  rw [denoteArrow_unpack]
  change M.compose (M.leftUnitorInv (product A B))
    (M.compose (M.associatorInv Silmaril.unit A B)
      (M.compose (split M.toSeqData (Syntactic.pairSplit (product A B) A B).symm)
        (M.tensor (Denotation.denote M.toSeqData K (Syntactic.rightParameter (product A B) A B e))
          (Denotation.denote M.toSeqData K (Syntactic.leftParameter (product A B) A B e))))) = _
  rw [denote_rightParameter, denote_leftParameter,
    ← split_symm M.toSeqData (Syntactic.pairSplit (product A B) A B)]
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let B' : M.toSeqData.PureObject := ⟨B⟩
  let I : M.toSeqData.PureObject := 𝟙_ M.toSeqData.PureObject
  have hn : M.compose (M.braiding (product Silmaril.unit A) (product Silmaril.unit B))
      (M.tensor (M.leftUnitor B) (M.leftUnitor A)) =
    M.compose (M.tensor (M.leftUnitor A) (M.leftUnitor B)) (M.braiding A B) :=
    (congrArg Subtype.val (CategoryTheory.BraidedCategory.braiding_naturality (λ_ A').hom (λ_ B').hom)).symm
  have hp : M.compose (split M.toSeqData (Syntactic.pairSplit (product A B) A B))
      (M.tensor (M.leftUnitor A) (M.leftUnitor B)) = M.right (M.leftUnitor A) B := by
    change M.compose
      (M.compose (M.right (M.compose (M.right (M.leftUnitorInv Silmaril.unit) A)
        (M.compose (M.associator Silmaril.unit Silmaril.unit A)
          (M.compose (M.left Silmaril.unit (M.braiding Silmaril.unit A))
            (M.associatorInv Silmaril.unit A Silmaril.unit)))) B)
        (M.associator (product Silmaril.unit A) Silmaril.unit B))
      (M.tensor (M.leftUnitor A) (M.leftUnitor B)) = _
    have hh : (((λ_ I).inv ▷ A' ≫ (α_ I I A').hom ≫ I ◁ (CategoryTheory.BraidedCategory.braiding I A').hom ≫
        (α_ I A' I).inv) ▷ B' ≫ (α_ (I ⊗ A') I B').hom) ≫
        ((λ_ A').hom ⊗ₘ (λ_ B').hom) = (λ_ A').hom ▷ B' := by
      simp only [I, braiding_tensorUnit_left, Category.assoc]
      monoidal
    exact congrArg Subtype.val hh
  change M.compose (M.leftUnitorInv (product A B))
    (M.compose (M.associatorInv Silmaril.unit A B)
      (M.compose (M.compose (split M.toSeqData (Syntactic.pairSplit (product A B) A B))
        (M.braiding (product Silmaril.unit A) (product Silmaril.unit B)))
        (M.tensor (M.leftUnitor B) (M.leftUnitor A)))) = _
  rw [M.toSeqData.compose_assoc (split M.toSeqData _), hn,
    ← M.toSeqData.compose_assoc (split M.toSeqData _), hp]
  have h : (λ_ (A' ⊗ B')).inv ≫ (α_ I A' B').inv ≫ (λ_ A').hom ▷ B' ≫ (CategoryTheory.BraidedCategory.braiding A' B').hom =
      (CategoryTheory.BraidedCategory.braiding A' B').hom := by
    have hc : (λ_ (A' ⊗ B')).inv ≫ (α_ I A' B').inv ≫ (λ_ A').hom ▷ B' = 𝟙 (A' ⊗ B') := by monoidal
    simpa only [Category.assoc, Category.id_comp] using congrArg (fun f => f ≫ (CategoryTheory.BraidedCategory.braiding A' B').hom) hc
  exact congrArg Subtype.val h

end Silmaril.Isotope.Refinement.Models.Interpretation

module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Uniformity.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Uniformity

/-! # Soundness of the local one-block pure simulation

The simulation premise compares the two typed step bodies. It acts on the
local feedback label and forwards the outward exits. The conclusion compares
the feedback computations entered at the original value and at its pure
image.

[Companion uniformity primitive](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/Uniform.lean#L40)
-/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.Uniformity

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd lift)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend duplicate caseWithContext contextualLoop splitMapCoprod)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel
    routeEnvironment)

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ]

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

variable {Γ : VCtx τ} {L : LCtx τ} {A D : τ}

/-- A pure state change lifts a commuting dispatcher square to the actual
typed feedback terms when the transported capture diagonal is central. -/
theorem sound_of_dispatcher
    (central : PremonoidalCategory.IsCentral (J.map (duplicate (ctxObj M Γ)) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) (ctxObj M Γ) (ctxObj M Γ)).inv))
    {p q : Region Φ} {t : Tm Φ}
    (hp : Region.HasType (A :: Γ) p (A :: L))
    (hq : Region.HasType (D :: Γ) q (D :: L))
    {ht : Tm.HasType (A :: Γ) t D} {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h)) (comm : localSimulation M J hp hq h) :
    denoteRegion J M (enterSingle_typed (.var (i := 0) rfl) hp) =
      denoteRegion J M (enterSingle_typed ht hq) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Uniformity.sound_of_dispatcher M J central hp hq dt comm

variable [FreydCategory.CentralUnit J]

/-- For constructor-valued producer branches, a typed literal-substitution
square in CFG η suffices under equality-induced tensor comparisons. -/
theorem sound
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {p q : Region Φ} {t : Tm Φ}
    (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : Region.HasType (D :: Γ) q (D :: L))
    {ht : Tm.HasType (A :: Γ) t D} {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h))
    (simulation : Region.CfgEta.Eqv (A :: Γ)
      (p.lsubst (Region.liftLSubstVars (localMap t)))
      ((Region.br 0 t).lsubst (Region.liftLSubstVars (fun _ => q))) (D :: L)) :
    denoteRegion J M (enterSingle_typed (.var (i := 0) rfl) hp.hasType) =
      denoteRegion J M (enterSingle_typed ht hq) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Uniformity.sound M J shared hp hq dt simulation


/-- The feedback state type can change while outward labels retain their types. -/
theorem localMap_typed {t : Tm Φ} (ht : Tm.HasType (A :: Γ) t D) :
    Region.LSubst.HasType Γ (A :: L) (D :: L) (localMap t) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Uniformity.localMap_typed ht

/-- Soundness of the one-block pure simulation rule from the denotations of
its two typed step terms. This supplies the rule case of a soundness
induction for a presentation extending CFG η. -/
theorem sound_entry_of_denotations
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {β p q : Region Φ} {t : Tm Φ}
    (hβ : ValueBranches Γ β (A :: L))
    (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : Region.HasType (D :: Γ) q (D :: L))
    {ht : Tm.HasType (A :: Γ) t D} {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h))
    (hl : Region.HasType (A :: Γ) (p.lsubst (Region.liftLSubstVars (localMap t))) (D :: L))
    (hr : Region.HasType (A :: Γ)
      ((Region.br 0 t).lsubst (Region.liftLSubstVars (fun _ => q))) (D :: L))
    (square : denoteRegion J M hl = denoteRegion J M hr) :
    denoteRegion J M (.cfg (fun _ : Fin 1 => A) hβ.hasType (fun _ => hp.hasType)) =
    denoteRegion J M (.cfg (fun _ : Fin 1 => D) (hβ.hasType.lsubst (localMap_typed ht))
      (fun _ => hq)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Uniformity.sound_entry_of_denotations M J shared hβ hp hq dt hl hr square

/-- The local pure simulation square can change the state of any one-block
CFG whose entry and first step have constructor-valued branch arguments. -/
theorem sound_entry
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {β p q : Region Φ} {t : Tm Φ}
    (hβ : ValueBranches Γ β (A :: L))
    (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : Region.HasType (D :: Γ) q (D :: L))
    {ht : Tm.HasType (A :: Γ) t D} {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h))
    (simulation : Region.CfgEta.Eqv (A :: Γ)
      (p.lsubst (Region.liftLSubstVars (localMap t)))
      ((Region.br 0 t).lsubst (Region.liftLSubstVars (fun _ => q))) (D :: L)) :
    denoteRegion J M (.cfg (fun _ : Fin 1 => A) hβ.hasType (fun _ => hp.hasType)) =
    denoteRegion J M (.cfg (fun _ : Fin 1 => D) (hβ.hasType.lsubst (localMap_typed ht))
      (fun _ => hq)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Uniformity.sound_entry M J shared hβ hp hq dt simulation

/-- An arbitrary exactly typed entry may first bind its branch arguments.
The state change then consumes the evaluated payload at the local label. -/
theorem sound_entry_afterBinding
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {β p q : Region Φ} {t : Tm Φ}
    (hβ : Region.HasType Γ β (A :: L))
    (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : Region.HasType (D :: Γ) q (D :: L))
    {ht : Tm.HasType (A :: Γ) t D} {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h))
    (simulation : Region.CfgEta.Eqv (A :: Γ)
      (p.lsubst (Region.liftLSubstVars (localMap t)))
      ((Region.br 0 t).lsubst (Region.liftLSubstVars (fun _ => q))) (D :: L)) :
    denoteRegion J M (.cfg (fun _ : Fin 1 => A) hβ (fun _ => hp.hasType)) =
    denoteRegion J M (.cfg (fun _ : Fin 1 => D)
      (hβ.bindBranchArguments.hasType.lsubst (localMap_typed ht)) (fun _ => hq)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Uniformity.sound_entry_afterBinding M J shared hβ hp hq dt simulation
end Silmaril.Isotope.LambdaSSA.Region.CfgEta.Uniformity

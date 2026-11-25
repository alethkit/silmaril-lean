module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgReification

/-! # Exact packed denotation of a one-block CFG -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.Extension.Singleton
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

section Congruence

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The linked decoder preserves the constructor-valued branch boundary. -/
theorem decodeExits_typed {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (h : ValueBranches Γ r [packedExitType L]) : ValueBranches Γ (decodeExits r L) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgReification.decodeExits_typed h

/-- The outer CFG retains the exact singleton interface of the packed assembly. -/
theorem guardedCfg_typed {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    ValueBranches [X] (guardedCfg S D e b) [D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgReification.guardedCfg_typed he hb

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

/-- The captured one-block assembly respects opt-in equality of the packed
entry and step. The result uses the same state and exit types. -/
theorem guardedCfg_map_congr {X S D : τ} {e e' b b' : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (he' : ValueBranches [X] e' [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]])
    (hb' : ValueBranches [Silmaril.product X S] b' [packedExitType [S, D]])
    (ee : ofRegion Seed he = ofRegion Seed he')
    (eb : ofRegion Seed hb = ofRegion Seed hb') :
    ofRegion Seed (guardedCfg_typed he hb) = ofRegion Seed (guardedCfg_typed he' hb') :=
  (ofRegion_eq_iff Seed _ _).2 (Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgReification.guardedCfg_congr
    Seed ((ofRegion_eq_iff Seed he he').1 ee) ((ofRegion_eq_iff Seed hb hb').1 eb))

end Congruence

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- The actual one-block CFG factors through its packed entry and local
block, with the original input retained on every feedback edge. -/
theorem denote_cfg {X S D : τ} {e b : Region Φ}
    (he : HasType [X] e [S, D]) (hb : HasType [S, X] b [S, D]) :
    denoteSingletonRegion J M (.cfg (fun _ : Fin 1 => S) he (fun _ => hb)) =
      assemble J M X S D (packedInputType [S, X]) (inputRecordIso M [S, X]).hom
        (denoteSingletonRegion J M (entry_typed he))
        (denoteSingletonRegion J M (block_typed hb)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgReification.denote_cfg J M he hb

/-- The guarded assembly from singleton representatives has the exact
denotation obtained by running the packed entry and threaded block arrows. -/
theorem denote_guardedCfg {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    denoteSingletonRegion J M (guardedCfg_typed he hb).hasType =
      assemble J M X S D (Silmaril.product X S)
        (((λ_ (M.obj X)).hom ▷ M.obj S) ≫ (M.productIso X S).inv)
        (denoteSingletonRegion J M he.hasType) (denoteSingletonRegion J M hb.hasType) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgReification.denote_guardedCfg
    J M he hb

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

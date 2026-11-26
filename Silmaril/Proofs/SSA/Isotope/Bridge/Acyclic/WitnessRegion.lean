module

public import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.WitnessLabels
public import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.WitnessTerm

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical
open scoped MonoidalCategory

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  (M : TypeModel υ V) (I : InstructionModel J M Q.Instr)

private def RegionImage (Γ : LambdaSSA.VCtx τ) (r : LambdaSSA.Region P.Instr)
    (L' : LambdaSSA.LCtx υ) {X : Type} (f : X) : Prop :=
  ∃ (hr : LambdaSSA.Region.HasType (Γ.map g.ty) (r.mapInstr g.instr) L')
    (a : J.obj (ctxObj M (Γ.map g.ty)) ⟶ J.obj (labelObj M L')),
    (letI := I; RegionDenotes J M hr a) ∧ HEq f a

omit [TypeFormers τ] [g.PreservesProducts] [g.PreservesSums] in
private theorem retargetRegion {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr}
    {L L' : LambdaSSA.LCtx υ} {X : Type} {f : X} (e : L = L')
    (a : RegionImage g M I Γ r L f) : RegionImage g M I Γ r L' f :=
  e ▸ a

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem cfgLabelObj_eq {n : Nat} (R : Fin n → τ) (L : LambdaSSA.LCtx τ) :
    labelObj (pullbackTypes g M) (List.ofFn R ++ L) =
      labelObj M (List.ofFn (g.ty ∘ R) ++ L.map g.ty) :=
  (labelObj_pullback g M _).trans (congrArg (labelObj M) (map_local_layout g R L))

omit [SymmetricCategory V] [DistributiveTensor V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] in
private theorem relabelCollective {n : Nat} {Γ : LambdaSSA.VCtx τ} {R : Fin n → τ}
    {L : LambdaSSA.LCtx τ}
    {fb : ∀ i, J.obj (ctxObj (pullbackTypes g M) (R i :: Γ)) ⟶
      J.obj (labelObj (pullbackTypes g M) (List.ofFn R ++ L))}
    {fb' : ∀ i, J.obj (ctxObj M ((g.ty ∘ R) i :: Γ.map g.ty)) ⟶
      J.obj (labelObj M (List.ofFn (g.ty ∘ R) ++ L.map g.ty))}
    {f : J.obj (ctxObj (pullbackTypes g M) Γ ⊗ finiteLabelObj (pullbackTypes g M) R) ⟶
      J.obj (labelObj (pullbackTypes g M) (List.ofFn R ++ L))}
    (d : CollectiveDenotes J (pullbackTypes g M) Γ R L fb f)
    (eb : ∀ i, HEq (fb i) (fb' i)) :
    ∃ f' : J.obj (ctxObj M (Γ.map g.ty) ⊗ finiteLabelObj M (g.ty ∘ R)) ⟶
        J.obj (labelObj M (List.ofFn (g.ty ∘ R) ++ L.map g.ty)),
      CollectiveDenotes J M (Γ.map g.ty) (g.ty ∘ R) (L.map g.ty) fb' f' ∧ HEq f f' := by
  have hΓ := ctxObj_pullback g M Γ
  have hL := cfgLabelObj_eq g M R L
  have hd := congrArg (fun E => E ⊗ finiteLabelObj M (g.ty ∘ R)) hΓ
  let f' := cast (congrArg₂ (fun X Y : V => J.obj X ⟶ J.obj Y) hd hL) f
  have hf : HEq f f' := (cast_heq _ _).symm
  refine ⟨f', ⟨?_⟩, hf⟩
  intro i
  have hΓi := ctxObj_pullback g M (R i :: Γ)
  have hi : HEq
      (J.map ((𝟙 (ctxObj (pullbackTypes g M) Γ)) ⊗ₘ finiteLabelInject (pullbackTypes g M) R i) ≫ f)
      (J.map ((𝟙 (ctxObj M (Γ.map g.ty))) ⊗ₘ finiteLabelInject M (g.ty ∘ R) i) ≫ f') := by
    congr! (config := .unfoldSameFun)
  exact eq_of_heq (hi.symm.trans ((heq_of_eq (d.restrict i)).trans (eb i)))

private theorem mapRegionWitness_image {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr}
    {L : LambdaSSA.LCtx τ} {hr : LambdaSSA.Region.HasType Γ r L}
    {f : J.obj (ctxObj (pullbackTypes g M) Γ) ⟶ J.obj (labelObj (pullbackTypes g M) L)}
    (d : letI := pullbackInstructions g I; RegionDenotes J (pullbackTypes g M) hr f) :
    RegionImage g M I Γ r (L.map g.ty) f := by
  let _ := I
  induction d with
  | @br Γ t A ht ft L i hl dt =>
    obtain ⟨_, ft', dt', et⟩ := mapTermWitness_proof g M I dt
    refine ⟨_, _, RegionDenotes.br (h := mapContextLookup g.ty hl) dt', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have hL := labelObj_pullback g M L
    have hi := labelInject_heq g M hl
    congr! (config := .unfoldSameFun)
  | @case Γ e A B he fe l L hl fl r hr fr de dl dr ihl ihr =>
    have deMap := mapTermWitness_proof g M I de
    obtain ⟨_, fe', de', ee⟩ := retargetTermWitness g M I
      (SignatureMap.PreservesSums.coprod (g := g) A B) deMap
    obtain ⟨_, fl', dl', el⟩ := ihl
    obtain ⟨_, fr', dr', er⟩ := ihr
    refine ⟨_, _, RegionDenotes.case de' dl' dr', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have hΓA := ctxObj_pullback g M (A :: Γ)
    have hΓB := ctxObj_pullback g M (B :: Γ)
    have hL := labelObj_pullback g M L
    have hc := coprod_hom_heq g M A B
    have ho := model_coprod_obj_eq g M A B
    congr! (config := .unfoldSameFun)
  | @let₁ Γ a A ha fa b L hb fb da db ih =>
    obtain ⟨_, fa', da', ea⟩ := mapTermWitness_proof g M I da
    obtain ⟨_, fb', db', eb⟩ := ih
    refine ⟨_, _, RegionDenotes.let₁ da' db', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have hΓA := ctxObj_pullback g M (A :: Γ)
    have hL := labelObj_pullback g M L
    congr! (config := .unfoldSameFun)
  | @let₂ Γ a A B ha fa b L hb fb da db ih =>
    have daMap := mapTermWitness_proof g M I da
    obtain ⟨_, fa', da', ea⟩ := retargetTermWitness g M I
      (SignatureMap.PreservesProducts.product (g := g) A B) daMap
    obtain ⟨_, fb', db', eb⟩ := ih
    refine ⟨_, _, RegionDenotes.let₂ da' db', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have hΓAB := ctxObj_pullback g M (B :: A :: Γ)
    have hL := labelObj_pullback g M L
    have hi := ctxPairIso_heq g M Γ A B
    have hp := product_hom_heq g M A B
    have ho := model_product_obj_eq g M A B
    congr! (config := .unfoldSameFun)
  | @cfgZero Γ L entry R blocks he hb fe de ih =>
    obtain ⟨he', fe', de', ee⟩ := ih
    exact ⟨_, _, RegionDenotes.cfgZero (R := g.ty ∘ R) (L := L.map g.ty)
      he' (fun i => Fin.elim0 i) de', ee⟩
  | @cfg n R Γ L entry blocks he hb fe fb collective de db dc ihe ihb =>
    have hLayout := map_local_layout g R L
    obtain ⟨he', fe', de', ee⟩ := retargetRegion g M I hLayout ihe
    have blockImage (i : Fin (n + 1)) :=
      retargetRegion g M I hLayout (ihb i)
    choose hb' fb' db' eb using blockImage
    obtain ⟨fc', dc', ec⟩ := relabelCollective g M dc eb
    refine ⟨_, _, RegionDenotes.cfg he' hb' de' db' dc', ?_⟩
    have hΓ := ctxObj_pullback g M Γ
    have hL := labelObj_pullback g M L
    have hCfg := cfgLabelObj_eq g M R L
    have hR : labelObj (pullbackTypes g M) (List.ofFn R) = labelObj M (List.ofFn (g.ty ∘ R)) :=
      (labelObj_pullback g M (List.ofFn R)).trans (congrArg (labelObj M) List.map_ofFn)
    have hs := labelAppendSplit_heq g M R L
    have ht := labelObjToFinite_heq g M R
    congr! (config := .unfoldSameFun)

theorem mapRegionWitness_proof {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr}
    {L : LambdaSSA.LCtx τ} {hr : LambdaSSA.Region.HasType Γ r L}
    {f : J.obj (ctxObj (pullbackTypes g M) Γ) ⟶ J.obj (labelObj (pullbackTypes g M) L)}
    (d : letI := pullbackInstructions g I; RegionDenotes J (pullbackTypes g M) hr f) :
    ∃ a : J.obj (ctxObj M (Γ.map g.ty)) ⟶ J.obj (labelObj M (L.map g.ty)),
      (letI := I; RegionDenotes J M (mapRegionTyping g hr) a) ∧ HEq f a := by
  obtain ⟨_, a, da, e⟩ := mapRegionWitness_image g M I d
  exact ⟨a, da, e⟩

end Silmaril.Isotope.Institution.Acyclic

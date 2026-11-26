module

public import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TypeChangeLetCase

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Morphism (SignatureMap)
open Theory (TypingIndex)
open Isotope.LetCase.LocallyNameless
open Silmaril.Logic.Metatheory.TheoryModel
open LetIter.Semantics.Categorical (TypeModel boundObj boundLookup boundVar envObj envSnocIso envPairHom)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "Δ₀" => (Ctx.nil : Ctx Empty υ)
local notation "S₀" => Models.signature P.Instr Γ₀

private theorem boundObj_eq (M : TypeModel υ V) {n : Nat} (β : BoundCtx τ n) :
    boundObj (pullbackTypes g M) β = boundObj M (β.mapTypes g.ty) := by
  induction β with
  | nil => rfl
  | snoc β A ih =>
    exact congrArg (fun X => X ⊗ M.obj (g.ty A)) ih

private theorem envObj_eq (M : TypeModel υ V) {n : Nat} (β : BoundCtx τ n) :
    envObj (pullbackTypes g M) Γ₀ β = envObj M Δ₀ (β.mapTypes g.ty) :=
  congrArg (fun X => (𝟙_ V) ⊗ X) (boundObj_eq g M β)

private theorem boundLookup_heq (M : TypeModel υ V) {n : Nat} (β : BoundCtx τ n) (i : Fin n) :
    HEq (boundLookup (pullbackTypes g M) (β := β) i) (boundLookup M (β := β.mapTypes g.ty) i) := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih =>
    have e := boundObj_eq g M β
    refine Fin.cases ?_ (fun k => ?_) i
    · change HEq (CartesianMonoidalCategory.snd (boundObj (pullbackTypes g M) β) (M.obj (g.ty A)))
        (CartesianMonoidalCategory.snd (boundObj M (β.mapTypes g.ty)) (M.obj (g.ty A)))
      congr! (config := .unfoldSameFun)
    · have hk := ih k
      have hA := congrArg M.obj (BoundCtx.get_mapTypes g.ty β k).symm
      change HEq
        (CartesianMonoidalCategory.fst (boundObj (pullbackTypes g M) β) (M.obj (g.ty A)) ≫
          boundLookup (pullbackTypes g M) k)
        (CartesianMonoidalCategory.fst (boundObj M (β.mapTypes g.ty)) (M.obj (g.ty A)) ≫
          boundLookup M k)
      congr! (config := .unfoldSameFun)

private theorem envSnocIso_heq (M : TypeModel υ V) {n : Nat} (β : BoundCtx τ n) (A : τ) :
    HEq (envSnocIso (pullbackTypes g M) Γ₀ β A)
      (envSnocIso M Δ₀ (β.mapTypes g.ty) (g.ty A)) := by
  unfold envSnocIso
  have e := boundObj_eq g M β
  congr! (config := .unfoldSameFun)

private theorem envPairHom_heq (M : TypeModel υ V) {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    HEq (envPairHom (pullbackTypes g M) Γ₀ β A B)
      (envPairHom M Δ₀ (β.mapTypes g.ty) (g.ty A) (g.ty B)) := by
  unfold envPairHom
  have e := boundObj_eq g M β
  have eΓ := envObj_eq g M β
  have eβ := boundObj_eq g M ((β.snoc A).snoc B)
  have eΓAB := envObj_eq g M ((β.snoc A).snoc B)
  congr! (config := .unfoldSameFun)

omit [CartesianMonoidalCategory V] [HasFiniteCoproducts V] in
private theorem iso_transport {A B D : V} (h : A = B) (i : B ≅ D) :
    HEq (eqToIso h ≪≫ i) i := by
  subst B
  simp [Iso.refl_trans]

omit [CartesianMonoidalCategory V] [HasFiniteCoproducts V] in
private theorem initial_transport {A B D : V} (h : A = B) (i : IsInitial B) :
    HEq ((cast (congrArg IsInitial h.symm) i).to D) (i.to D) := by
  subst B
  rfl

variable [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

private theorem algebraExt {I : Type}
    {T : Silmaril.Logic.Metatheory.TheoryModel.Signature.{0, 0} I}
    {M N : Algebra.{0, 0, 0} T} (ec : M.Carrier = N.Carrier)
    (ho : ∀ {i} (o : T.Op i)
      (a : ∀ j, M.Carrier (T.argSort o j)) (b : ∀ j, N.Carrier (T.argSort o j)),
      (∀ j, HEq (a j) (b j)) → HEq (M.op o a) (N.op o b)) :
    M = N := by
  cases M
  cases N
  cases ec
  congr 1
  funext i o a
  exact eq_of_heq (ho o a a fun _ => HEq.rfl)

local notation "pull" => fun (K : CoherentRegionModel J Q) => K.pullbackOfWitness g (regionWitnessPullback g K)

private theorem caseOperation_transport (K : CoherentRegionModel J Q)
    {i : TypingIndex τ} (o : (S₀).Op i)
    (a : ∀ j, K.caseAlgebra.Carrier (mapTypingIndex g ((S₀).argSort o j)))
    (b : ∀ j, (pull K).caseAlgebra.Carrier ((S₀).argSort o j))
    (ha : ∀ j, HEq (a j) (b j)) :
    HEq ((pull K).caseAlgebra.op o b) (K.caseAlgebra.op (mappedCaseOp g o).2
      (mappedCaseArgs g K.caseAlgebra o a)) := by
  have args (j : Fin (Models.Operation.arity (mappedCaseOp g o).2)) :
      HEq (b (Fin.cast (mappedCaseOp_arity g o) j)) (mappedCaseArgs g K.caseAlgebra o a j) :=
    (ha _).symm.trans (eqRec_heq (mappedCaseOp_args g o j) _).symm
  cases o with
  | @fv n β x A hx => exact x.elim
  | @bv n β i =>
    have hβ := boundObj_eq g K.types β
    have hΓ := envObj_eq g K.types β
    have hA := congrArg K.types.obj (BoundCtx.get_mapTypes g.ty β i).symm
    have hk := boundLookup_heq g K.types β i
    dsimp only [CoherentRegionModel.caseAlgebra, caseOperation, freydCaseOperation, mappedCaseOp, boundVar]
    congr! (config := .unfoldSameFun)
  | @op n β f =>
    have h0 := args (0 : Fin 1)
    have hΓ := envObj_eq g K.types β
    have hA := congrArg K.types.obj (g.source f).symm
    have hB := congrArg K.types.obj (g.target f).symm
    have hp : HEq ((pullbackInstructions g K.instructions).denote f)
        (K.instructions.denote (g.instr f)) := cast_heq _ _
    dsimp only [CoherentRegionModel.caseAlgebra, caseOperation, freydCaseOperation, mappedCaseOp]
    congr! (config := .unfoldSameFun)
  | @let₁ n β A B =>
    have h0 := args (0 : Fin 2)
    have h1 := args (1 : Fin 2)
    have hΓ := envObj_eq g K.types β
    have hΓA := envObj_eq g K.types (β.snoc A)
    have hi := envSnocIso_heq g K.types β A
    dsimp only [CoherentRegionModel.caseAlgebra, caseOperation, freydCaseOperation, mappedCaseOp]
    congr! (config := .unfoldSameFun)
  | @unit n β =>
    have hΓ := envObj_eq g K.types β
    have hu := congrArg K.types.obj (SignatureMap.PreservesProducts.unit (g := g))
    have hi : HEq (pullbackTypes g K.types).unitIso K.types.unitIso := iso_transport hu _
    dsimp only [CoherentRegionModel.caseAlgebra, caseOperation, freydCaseOperation, mappedCaseOp]
    congr! (config := .unfoldSameFun)
  | @pair n β A B =>
    have h0 := args (0 : Fin 2)
    have h1 := args (1 : Fin 2)
    have hΓ := envObj_eq g K.types β
    have hp := congrArg K.types.obj (SignatureMap.PreservesProducts.product (g := g) A B)
    have hi : HEq ((pullbackTypes g K.types).productIso A B)
        (K.types.productIso (g.ty A) (g.ty B)) := iso_transport hp _
    dsimp only [CoherentRegionModel.caseAlgebra, caseOperation, freydCaseOperation, mappedCaseOp]
    congr! (config := .unfoldSameFun)
  | @let₂ n β A B D =>
    have h0 := args (0 : Fin 2)
    have h1 := args (1 : Fin 2)
    have hΓ := envObj_eq g K.types β
    have hΓAB := envObj_eq g K.types ((β.snoc A).snoc B)
    have hp := congrArg K.types.obj (SignatureMap.PreservesProducts.product (g := g) A B)
    have hi : HEq ((pullbackTypes g K.types).productIso A B)
        (K.types.productIso (g.ty A) (g.ty B)) := iso_transport hp _
    have he := envPairHom_heq g K.types β A B
    dsimp only [CoherentRegionModel.caseAlgebra, caseOperation, freydCaseOperation, mappedCaseOp]
    congr! (config := .unfoldSameFun)
  | @inl n β A B | @inr n β A B =>
    have h0 := args (0 : Fin 1)
    have hΓ := envObj_eq g K.types β
    have hc := congrArg K.types.obj (SignatureMap.PreservesSums.coprod (g := g) A B)
    have hi : HEq ((pullbackTypes g K.types).coprodIso A B)
        (K.types.coprodIso (g.ty A) (g.ty B)) := iso_transport hc _
    dsimp only [CoherentRegionModel.caseAlgebra, caseOperation, freydCaseOperation, mappedCaseOp]
    congr! (config := .unfoldSameFun)
  | @case n β A B D =>
    have h0 := args (0 : Fin 3)
    have h1 := args (1 : Fin 3)
    have h2 := args (2 : Fin 3)
    have hΓ := envObj_eq g K.types β
    have hΓA := envObj_eq g K.types (β.snoc A)
    have hΓB := envObj_eq g K.types (β.snoc B)
    have hc := congrArg K.types.obj (SignatureMap.PreservesSums.coprod (g := g) A B)
    have hi : HEq ((pullbackTypes g K.types).coprodIso A B)
        (K.types.coprodIso (g.ty A) (g.ty B)) := iso_transport hc _
    have hs := envSnocIso_heq g K.types β A
    have ht := envSnocIso_heq g K.types β B
    dsimp only [CoherentRegionModel.caseAlgebra, caseOperation, freydCaseOperation, mappedCaseOp]
    congr! (config := .unfoldSameFun)
  | @abort n β A =>
    have h0 := args (0 : Fin 1)
    have hΓ := envObj_eq g K.types β
    have he := congrArg K.types.obj (SignatureMap.PreservesSums.empty (g := g))
    have hi : HEq ((pullbackTypes g K.types).emptyIsInitial.to (K.types.obj (g.ty A)))
        (K.types.emptyIsInitial.to (K.types.obj (g.ty A))) :=
      initial_transport he K.types.emptyIsInitial
    dsimp only [CoherentRegionModel.caseAlgebra, caseOperation, freydCaseOperation, mappedCaseOp]
    congr! (config := .unfoldSameFun)

theorem caseAlgebra_pullback_proof (K : CoherentRegionModel J Q) :
    Algebra.reductObj (typeCaseSignatureHom g) K.caseAlgebra = (pull K).caseAlgebra := by
  apply algebraExt
  · funext i
    rcases i with ⟨n, β, A⟩
    exact congrArg (fun X => J.obj X ⟶ J.obj (K.types.obj (g.ty A))) (envObj_eq g K.types β).symm
  · intro i o a b h
    exact (typeCaseHom_reductOp_heq g K.caseAlgebra o a).trans (caseOperation_transport g K o a b h).symm

end Silmaril.Isotope.Institution.Acyclic

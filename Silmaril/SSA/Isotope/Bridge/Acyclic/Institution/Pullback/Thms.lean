module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Pullback

/-! # Dependent model pullback and exact equation satisfaction -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Corridor)
open Morphism (SignatureMap)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical (ctxObj labelObj RegionTypingCoherent denoteRegion)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
  [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V] {J : V ⥤ C}

@[simp] theorem pullbackTypes_id (M : TypeModel τ V) :
    pullbackTypes (P := P) (Q := P) SignatureMap.id M = M :=
  pullbackTypes_id_proof M

/-- The composite pulls back the chosen type-former isomorphisms strictly. -/
theorem pullbackTypes_comp (M : TypeModel κ V) :
    pullbackTypes (h.comp g) M = pullbackTypes g (pullbackTypes h M) :=
  pullbackTypes_comp_proof g h M

/-- Primitive interpretations restrict along the identity over the identity type model. -/
theorem pullbackInstructions_id {M : TypeModel τ V} (I : InstructionModel J M P.Instr) :
    HEq (pullbackInstructions (P := P) (Q := P) SignatureMap.id I) I :=
  pullbackInstructions_id_proof I

/-- Primitive interpretations compose over the equality of the dependent type models. -/
theorem pullbackInstructions_comp {M : TypeModel κ V} (I : InstructionModel J M S.Instr) :
    HEq (pullbackInstructions (h.comp g) I) (pullbackInstructions g (pullbackInstructions h I)) :=
  pullbackInstructions_comp_proof g h I

/-- A mapped SSA value context interprets as the same tensor of value objects. -/
theorem ctxObj_pullback (M : TypeModel υ V) (Γ : LambdaSSA.VCtx τ) :
    ctxObj (pullbackTypes g M) Γ = ctxObj M (Γ.map g.ty) :=
  ctxObj_pullback_proof g M Γ

/-- The diagrams indexing a source exit coproduct and its mapped target
coproduct have the same objects in the same order. -/
theorem labelFamily_pullback (M : TypeModel υ V) (L : LambdaSSA.LCtx τ) :
    HEq (fun i : Fin L.length => (pullbackTypes g M).obj (L.get i))
      (fun j : Fin (L.map g.ty).length => M.obj ((L.map g.ty).get j)) :=
  labelFamily_pullback_proof g M L

/-- A mapped exit context interprets as the same finite coproduct. The
coproduct diagram is identified using the equality of list lengths. -/
theorem labelObj_pullback (M : TypeModel υ V) (L : LambdaSSA.LCtx τ) :
    labelObj (pullbackTypes g M) L = labelObj M (L.map g.ty) :=
  labelObj_pullback_proof g M L

omit [TypeFormers τ] [TypeFormers υ] in
/-- Type translation preserves a value or label lookup at its original index. -/
theorem mapContextLookup (f : τ → υ) {L : List τ} {i : Nat} {A : τ}
    (ha : LambdaSSA.At L i A) : LambdaSSA.At (L.map f) i (f A) :=
  mapContextLookup_proof f ha

/-- Relabelling preserves positional region typing, including local layouts. -/
theorem mapRegionTyping {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr}
    {L : LambdaSSA.LCtx τ} (hr : LambdaSSA.Region.HasType Γ r L) :
    LambdaSSA.Region.HasType (Γ.map g.ty) (r.mapInstr g.instr) (L.map g.ty) :=
  mapRegionTyping_proof g hr

/-- Compilation commutes with the type-changing map on exact equations. -/
theorem compile_mapSSASignature (e : SSAEquation P) :
    compile (mapSSASignature g e) = mapCaseSignature g (compile e) :=
  compile_mapSSASignature_proof g e

/-- Reification commutes with the type-changing map on exact equations. -/
theorem reify_mapCaseSignature (e : CaseEquation P) :
    reify (mapCaseSignature g e) = mapSSASignature g (reify e) :=
  reify_mapCaseSignature_proof g e

section Regions

variable [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

/-- Transferring both witnesses to a coherent target is sufficient for source coherence. -/
theorem CoherentRegionModel.pullback_coherent (K : CoherentRegionModel J Q)
    (w : RegionWitnessPullback g K) :
    letI := pullbackInstructions g K.instructions
    RegionTypingCoherent (Φ := P.Instr) J (pullbackTypes g K.types) :=
  pullback_coherent_proof g K w

/-- The pulled-back model with coherence supplied by witness transport. -/
noncomputable def CoherentRegionModel.pullbackOfWitness (K : CoherentRegionModel J Q)
    (w : RegionWitnessPullback g K) : CoherentRegionModel J P :=
  K.pullback g (K.pullback_coherent g w)

/-- The existing fixed-type proof supplies the witness law for primitive maps. -/
theorem regionWitnessPullback_primitive {P Q : InstrSig τ ε} (f : P ⟶ Q)
    (K : CoherentRegionModel J Q) : RegionWitnessPullback f.toSignatureMap K :=
  regionWitnessPullback_primitive_proof f K

/-- The witness law holds on the identity map. -/
theorem regionWitnessPullback_id (K : CoherentRegionModel J P) :
    RegionWitnessPullback (P := P) (Q := P) SignatureMap.id K :=
  regionWitnessPullback_primitive (𝟙 P) K

/-- Witness transport is closed under composition with the intermediate pulled-back model. -/
theorem regionWitnessPullback_comp (K : CoherentRegionModel J S) (wh : RegionWitnessPullback h K)
    (wg : RegionWitnessPullback g (K.pullbackOfWitness h wh)) :
    RegionWitnessPullback (h.comp g) K :=
  regionWitnessPullback_comp_proof g h K wh wg

/-- For thin computation categories every type-changing map has witness transport:
there is at most one arrow between the transported endpoints. -/
theorem regionWitnessPullback_of_thin [Quiver.IsThin C] (K : CoherentRegionModel J Q) :
    RegionWitnessPullback g K :=
  regionWitnessPullback_of_thin_proof g K

/-- On the existing primitive signature category the pulled-back model
is exactly the model used by the fixed-type corridor. -/
theorem CoherentRegionModel.pullback_primitive {P Q : InstrSig τ ε} (f : P ⟶ Q)
    (K : CoherentRegionModel J Q) (coh : letI := pullbackInstructions f.toSignatureMap K.instructions
      RegionTypingCoherent (Φ := P.Instr) J (pullbackTypes f.toSignatureMap K.types)) :
    K.pullback f.toSignatureMap coh = K.reduct f :=
  pullback_primitive_proof f K coh

@[simp] theorem CoherentRegionModel.pullback_id (K : CoherentRegionModel J P)
    (coh : letI := pullbackInstructions (P := P) (Q := P) SignatureMap.id K.instructions
      RegionTypingCoherent (Φ := P.Instr) J
        (pullbackTypes (P := P) (Q := P) SignatureMap.id K.types)) :
    K.pullback (P := P) (Q := P) SignatureMap.id coh = K :=
  pullback_id_proof K coh

/-- Direct and iterated pullbacks agree independently of their coherence proofs. -/
theorem CoherentRegionModel.pullback_comp (K : CoherentRegionModel J S)
    (cohH : letI := pullbackInstructions h K.instructions
      RegionTypingCoherent (Φ := Q.Instr) J (pullbackTypes h K.types))
    (cohG : letI := pullbackInstructions g (K.pullback h cohH).instructions
      RegionTypingCoherent (Φ := P.Instr) J (pullbackTypes g (K.pullback h cohH).types))
    (cohHG : letI := pullbackInstructions (h.comp g) K.instructions
      RegionTypingCoherent (Φ := P.Instr) J (pullbackTypes (h.comp g) K.types)) :
    K.pullback (h.comp g) cohHG = (K.pullback h cohH).pullback g cohG :=
  pullback_comp_proof g h K cohH cohG cohHG

/-- Chosen region denotations agree after transport of context and exit objects. -/
theorem CoherentRegionModel.denoteRegion_pullback (K : CoherentRegionModel J Q)
    (w : RegionWitnessPullback g K)
    {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ}
    (hr : LambdaSSA.Region.HasType Γ r L) :
    HEq (letI := pullbackInstructions g K.instructions; denoteRegion J (pullbackTypes g K.types) hr)
      (letI := K.instructions; denoteRegion J K.types (mapRegionTyping g hr)) :=
  denoteRegion_pullback_proof g K w hr

/-- Witness transport is exactly source coherence together with preservation
of the selected region denotation at each typed judgement. -/
theorem regionWitnessPullback_iff (K : CoherentRegionModel J Q) :
    RegionWitnessPullback g K ↔
      (letI := pullbackInstructions g K.instructions
       RegionTypingCoherent (Φ := P.Instr) J (pullbackTypes g K.types)) ∧
      ∀ {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ}
        (hr : LambdaSSA.Region.HasType Γ r L),
        HEq (letI := pullbackInstructions g K.instructions; denoteRegion J (pullbackTypes g K.types) hr)
          (letI := K.instructions; denoteRegion J K.types (mapRegionTyping g hr)) :=
  regionWitnessPullback_iff_proof g K

/-- The typed single-exit translation commutes with dependent model pullback. -/
theorem CoherentRegionModel.denoteSSA_pullback (K : CoherentRegionModel J Q)
    (w : RegionWitnessPullback g K) {n : Nat} {β : BoundCtx τ n} {A : τ}
    (c : LambdaSSA.Acyclic.Code P.Instr β A) :
    HEq ((K.pullbackOfWitness g w).denoteSSA c) (K.denoteSSA (c.mapSignature g)) :=
  denoteSSA_pullback_proof g K w c

/-- Satisfaction of exact structured equations is invariant under the pullback. -/
theorem ssaSat_pullback (K : CoherentRegionModel J Q) (w : RegionWitnessPullback g K)
    (e : SSAEquation P) :
    let K' := K.pullbackOfWitness g w
    K.denoteSSA (mapSSASignature g e).2.1 = K.denoteSSA (mapSSASignature g e).2.2 ↔
      K'.denoteSSA e.2.1 = K'.denoteSSA e.2.2 :=
  ssaSat_pullback_proof g K w e

variable [FreydCategory.CentralUnit J]

/-- Satisfaction is also invariant in the corresponding actual LetCase algebras. -/
theorem caseSat_pullback (K : CoherentRegionModel J Q) (w : RegionWitnessPullback g K)
    (e : CaseEquation P) :
    ((LetCase.inst (Ctx.nil : Ctx Empty υ)).obj Q).Sat K.caseAlgebra (mapCaseSignature g e) ↔
      ((LetCase.inst (Ctx.nil : Ctx Empty τ)).obj P).Sat (K.pullbackOfWitness g w).caseAlgebra e :=
  caseSat_pullback_proof g K w e

/-- A type-changing map with witness transport gives a corridor of the exact SSA
rooms from the fixed-type institution. Composing it with `reifyCorridor` translates
LetCase sentences by `reify_mapCaseSignature`, and reduces models by
`CoherentRegionModel.pullbackOfWitness` followed by `caseAlgebra`. -/
noncomputable def ssaTypeCorridor (w : ∀ K : CoherentRegionModel J Q, RegionWitnessPullback g K) :
    ssaRoom J P ⟶ ssaRoom J Q where
  sen := mapSSASignature g
  mod := ShrinkHoms.inverse.{0} (Discrete (CoherentRegionModel J Q)) ⋙
    Discrete.functor (fun K => Discrete.mk (K.pullbackOfWitness g (w K))) ⋙
    ShrinkHoms.functor.{0} (Discrete (CoherentRegionModel J P))
  sat K e := ssaSat_pullback g K.fromShrinkHoms.as (w K.fromShrinkHoms.as) e

/-- The composite with the existing reification corridor has the expected
sentence component at the translated signature. -/
theorem reifyCorridor_typeChange_sen (w : ∀ K : CoherentRegionModel J Q, RegionWitnessPullback g K) :
    Corridor.sen (reifyCorridor J P ≫ ssaTypeCorridor g w) =
      (reifyCorridor J Q).sen ∘ mapCaseSignature g :=
  funext fun e => (reify_mapCaseSignature g e).symm

end Regions
end Silmaril.Isotope.Institution.Acyclic

module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Reduct.Defs

public section

set_option backward.isDefEq.respectTransparency false

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.Theory (TypingIndex)
open Isotope.LetCase.LocallyNameless
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical

variable {τ ε : Type} [TypeFormers τ] {P Q S : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  {M : TypeModel τ V}

private theorem relabel_op [InstructionModel J M Q.Instr]
    {Γ : LambdaSSA.VCtx τ} {a : LambdaSSA.Tm Q.Instr} {A B : τ}
    (f : Q.Instr) (hs : instrSrc f = A) (ht : instrTrg f = B)
    {ha : LambdaSSA.Tm.HasType Γ a A} {fa : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (da : Denotes J M ha fa) (h : LambdaSSA.Tm.HasType Γ (.op f a) B) :
    Denotes J M h (fa ≫ transportArrow (M := M) hs ht
      (InstructionModel.denote (J := J) (M := M) f)) := by
  cases hs
  cases ht
  exact .op da

private theorem relabel_term (g : P ⟶ Q) (I : InstructionModel J M Q.Instr)
    {Γ : LambdaSSA.VCtx τ} {a : LambdaSSA.Tm P.Instr} {A : τ}
    {ha : LambdaSSA.Tm.HasType Γ a A} {fa : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (da : letI := restrictInstructions g I; Denotes J M ha fa) :
    letI := I
    Denotes J M (ha.mapInstr (InstrSig.Hom.instr g) ⟨g.source, g.target⟩) fa := by
  let _ := I
  induction da with
  | var h => exact .var h
  | @op _ _ f _ _ _ ih =>
      exact relabel_op (g.instr f) (g.source f) (g.target f) ih _
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ iha ihb => exact .pair iha ihb
  | unit => exact .unit
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih

theorem relabel_region_proof (g : P ⟶ Q) (I : InstructionModel J M Q.Instr)
    {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ}
    {hr : LambdaSSA.Region.HasType Γ r L}
    {fr : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (dr : letI := restrictInstructions g I; RegionDenotes J M hr fr) :
    letI := I
    RegionDenotes J M (hr.mapInstr (InstrSig.Hom.instr g) ⟨g.source, g.target⟩) fr := by
  let _ := I
  induction dr with
  | br da => exact .br (relabel_term g I da)
  | case de _ _ ihl ihr => exact .case (relabel_term g I de) ihl ihr
  | let₁ da _ ih => exact .let₁ (relabel_term g I da) ih
  | let₂ da _ ih => exact .let₂ (relabel_term g I da) ih
  | cfgZero he hb _ ih =>
      exact .cfgZero (he.mapInstr g.instr ⟨g.source, g.target⟩)
        (fun i => (hb i).mapInstr g.instr ⟨g.source, g.target⟩) ih
  | cfg he hb _ _ dc ihE ihB =>
      exact .cfg (he.mapInstr g.instr ⟨g.source, g.target⟩)
        (fun i => (hb i).mapInstr g.instr ⟨g.source, g.target⟩) ihE ihB dc

theorem reduct_coherent_proof (g : P ⟶ Q) (K : CoherentRegionModel J Q) :
    letI := restrictInstructions g K.instructions
    RegionTypingCoherent (Φ := P.Instr) J K.types := by
  let _ := restrictInstructions g K.instructions
  refine ⟨?_⟩
  intro Γ r L h f h' df dh
  let _ := K.instructions
  let _ := K.coherent
  exact RegionTypingCoherent.denotes_eq (relabel_region_proof g K.instructions df)
    (relabel_region_proof g K.instructions dh)

theorem denoteRegion_reduct_proof (g : P ⟶ Q) (K : CoherentRegionModel J Q)
    {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ}
    (hr : LambdaSSA.Region.HasType Γ r L) :
    (letI := restrictInstructions g K.instructions; denoteRegion J K.types hr) =
    (letI := K.instructions
     denoteRegion J K.types (hr.mapInstr (InstrSig.Hom.instr g) ⟨g.source, g.target⟩)) := by
  have d := (let _ := restrictInstructions g K.instructions; denoteRegion_spec J K.types hr)
  let _ := K.instructions
  let _ := K.coherent
  exact (relabel_region_proof g K.instructions d).eq_denote J K.types

omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] in
private theorem transportArrow_comp {A B D X Y Z : τ} (h : A = B) (k : B = D)
    (h' : X = Y) (k' : Y = Z) (f : J.obj (M.obj A) ⟶ J.obj (M.obj X)) :
    transportArrow (M := M) k k' (transportArrow (M := M) h h' f) =
      transportArrow (M := M) (h.trans k) (h'.trans k') f := by
  cases h
  cases k
  cases h'
  cases k'
  rfl

omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] in
theorem restrictInstructions_comp_proof (f : P ⟶ Q) (g : Q ⟶ S)
    (I : InstructionModel J M S.Instr) :
    restrictInstructions (f ≫ g) I = restrictInstructions f (restrictInstructions g I) := by
  change InstructionModel.mk _ = InstructionModel.mk _
  congr 1
  funext op
  exact (transportArrow_comp (g.source (f.instr op)) (f.source op) (g.target (f.instr op))
    (f.target op) (I.denote (g.instr (f.instr op)))).symm

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

private theorem caseAlgebra_reduct_op (K : CoherentRegionModel J Q) {n : Nat}
    {β : BoundCtx τ n} {A B : τ} (f : Q.Instr)
    (ht : instrTrg f = A) (hs : instrSrc f = B)
    (a : caseArrow K ⟨n, β, B⟩)
    (args : (j : Fin ((Models.signature Q.Instr Γ₀).arity
      (castOp (Models.signature Q.Instr Γ₀)
        (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex τ)) ht) (Models.Operation.op f)))) →
      K.caseAlgebra.Carrier ((Models.signature Q.Instr Γ₀).argSort
        (castOp (Models.signature Q.Instr Γ₀)
          (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex τ)) ht) (Models.Operation.op f)) j))
    (hargs : ∀ j, HEq (args j) a) :
    K.caseAlgebra.op
      (castOp (Models.signature Q.Instr Γ₀)
        (congrArg (fun A => (⟨n, β, A⟩ : TypingIndex τ)) ht) (Models.Operation.op f)) args =
      a ≫ transportArrow (M := K.types) hs ht (K.instructions.denote f) := by
  subst A
  subst B
  change args (0 : Fin 1) ≫ K.instructions.denote f = a ≫ K.instructions.denote f
  rw [eq_of_heq (hargs (0 : Fin 1))]

theorem caseAlgebra_reduct_proof (g : P ⟶ Q) (K : CoherentRegionModel J Q) :
    Algebra.reductObj (LetCase.sigHom Γ₀ g) K.caseAlgebra =
      (⟨K.types, restrictInstructions g K.instructions, reduct_coherent_proof g K⟩ :
        CoherentRegionModel J P).caseAlgebra := by
  unfold Algebra.reductObj
  congr 1
  funext i o args
  cases o with
  | op f =>
      refine caseAlgebra_reduct_op K (g.instr f) (g.target f) (g.source f) (args 0) _
        (fun j => (eqRec_heq _ _).trans ?_)
      let k : Fin 1 := (LetCase.sigHom Γ₀ g).arg (.op f) j
      change HEq (args k) (args (0 : Fin 1))
      rw [Fin.eq_zero k]
  | fv | bv | let₁ | unit | pair | let₂ | inl | inr | case | abort => rfl

end Silmaril.Isotope.Institution.Acyclic

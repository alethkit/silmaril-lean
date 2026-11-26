module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical (ctxObj labelObj)
open scoped MonoidalCategory

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
  [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V] {J : V ⥤ C}

private theorem pullbackTypes_primitive {P Q : InstrSig τ ε} (f : P ⟶ Q)
    (M : TypeModel τ V) : pullbackTypes f.toSignatureMap M = M := by
  cases M
  dsimp only [pullbackTypes, InstrSig.Hom.toSignatureMap, Function.comp_id, id_eq]
  congr 1
  · funext A B
    exact Iso.refl_trans _
  · exact Iso.refl_trans _
  · funext A B
    exact Iso.refl_trans _

theorem pullbackTypes_id_proof (M : TypeModel τ V) :
    pullbackTypes (P := P) (Q := P) SignatureMap.id M = M :=
  pullbackTypes_primitive (𝟙 P) M

theorem pullbackTypes_comp_proof (M : TypeModel κ V) :
    pullbackTypes (h.comp g) M = pullbackTypes g (pullbackTypes h M) := by
  dsimp only [pullbackTypes, SignatureMap.comp, Function.comp_apply]
  congr 1
  · funext A B
    rw [← Iso.trans_assoc, eqToIso_trans]
  · rw [← Iso.trans_assoc, eqToIso_trans]
  · funext A B
    rw [← Iso.trans_assoc, eqToIso_trans]
  · apply Subsingleton.elim

private theorem instructions_heq {M N : TypeModel τ V} (hm : M = N)
    (I : InstructionModel J M P.Instr) (I' : InstructionModel J N P.Instr)
    (hd : ∀ f, HEq (I.denote f) (I'.denote f)) : HEq I I' := by
  subst N
  apply heq_of_eq
  cases I
  cases I'
  congr 1
  funext f
  exact eq_of_heq (hd f)

private theorem pullbackInstructions_primitive {P Q : InstrSig τ ε} (f : P ⟶ Q)
    {M : TypeModel τ V} (I : InstructionModel J M Q.Instr) :
    HEq (pullbackInstructions f.toSignatureMap I) (restrictInstructions f I) := by
  apply instructions_heq (pullbackTypes_primitive f M)
  intro a
  rfl

theorem pullbackInstructions_id_proof {M : TypeModel τ V} (I : InstructionModel J M P.Instr) :
    HEq (pullbackInstructions (P := P) (Q := P) SignatureMap.id I) I :=
  pullbackInstructions_primitive (𝟙 P) I

theorem pullbackInstructions_comp_proof {M : TypeModel κ V}
    (I : InstructionModel J M S.Instr) :
    HEq (pullbackInstructions (h.comp g) I) (pullbackInstructions g (pullbackInstructions h I)) := by
  apply instructions_heq (pullbackTypes_comp_proof g h M)
  intro f
  apply heq_of_eq
  change transportArrow (M := M) ((h.comp g).source f) ((h.comp g).target f)
      (I.denote (h.instr (g.instr f))) =
    transportArrow (M := pullbackTypes h M) (g.source f) (g.target f)
      (transportArrow (M := M) (h.source (g.instr f)) (h.target (g.instr f))
        (I.denote (h.instr (g.instr f))))
  unfold transportArrow
  rw [cast_cast]
  rfl

theorem ctxObj_pullback_proof (M : TypeModel υ V) (Γ : LambdaSSA.VCtx τ) :
    ctxObj (pullbackTypes g M) Γ = ctxObj M (Γ.map g.ty) := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih =>
    change ctxObj (pullbackTypes g M) Γ ⊗ M.obj (g.ty A) =
      ctxObj M (Γ.map g.ty) ⊗ M.obj (g.ty A)
    rw [ih]

omit [TypeFormers τ] [TypeFormers υ] in
theorem boundCtx_toList_mapTypes_proof (f : τ → υ) {n : Nat} (β : BoundCtx τ n) :
    (β.mapTypes f).toList = β.toList.map f := by
  induction β with
  | nil => rfl
  | snoc β A ih => exact congrArg (List.cons (f A)) ih

private theorem val_eq_of_heq {n m : Nat} (h : n = m) {i : Fin n} {j : Fin m}
    (he : HEq i j) : i.val = j.val := by
  subst m
  exact congrArg Fin.val (eq_of_heq he)

omit [CartesianMonoidalCategory V] in
private theorem coproduct_eq_of_heq {n m : Nat} (h : n = m) {F : Fin n → V} {G : Fin m → V}
    (he : HEq F G) : (∐ F) = (∐ G) := by
  subst m
  rw [eq_of_heq he]

theorem labelFamily_pullback_proof (M : TypeModel υ V) (L : LambdaSSA.LCtx τ) :
    HEq (fun i : Fin L.length => (pullbackTypes g M).obj (L.get i))
      (fun j : Fin (L.map g.ty).length => M.obj ((L.map g.ty).get j)) := by
  apply Function.hfunext (congrArg Fin (List.length_map g.ty).symm)
  intro i j hij
  have hj := val_eq_of_heq (List.length_map g.ty).symm hij
  simp only [List.get_eq_getElem, List.getElem_map, hj]
  rfl

theorem labelObj_pullback_proof (M : TypeModel υ V) (L : LambdaSSA.LCtx τ) :
    labelObj (pullbackTypes g M) L = labelObj M (L.map g.ty) :=
  coproduct_eq_of_heq (List.length_map g.ty).symm (labelFamily_pullback_proof g M L)

omit [TypeFormers τ] [TypeFormers υ] in
theorem mapContextLookup_proof (f : τ → υ) {L : List τ} {i : Nat} {A : τ}
    (ha : LambdaSSA.At L i A) : LambdaSSA.At (L.map f) i (f A) := by
  change (L.map f)[i]? = _
  rw [List.getElem?_map, ha]
  rfl

theorem mapTermTyping_proof {Γ : LambdaSSA.VCtx τ} {a : LambdaSSA.Tm P.Instr} {A : τ}
    (ha : LambdaSSA.Tm.HasType Γ a A) :
    LambdaSSA.Tm.HasType (Γ.map g.ty) (a.mapInstr g.instr) (g.ty A) := by
  induction ha with
  | var h => exact .var (mapContextLookup_proof g.ty h)
  | @op Γ a f _ ih =>
    change LambdaSSA.Tm.HasType _ (.op (g.instr f) _) (g.ty (instrTrg f))
    rw [← g.target f]
    exact .op (by simpa only [g.source f] using ih)
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ iha ihb => simpa only [LambdaSSA.Tm.mapInstr, SignatureMap.PreservesProducts.product] using
      LambdaSSA.Tm.HasType.pair iha ihb
  | unit => simpa only [LambdaSSA.Tm.mapInstr, SignatureMap.PreservesProducts.unit] using
      (LambdaSSA.Tm.HasType.unit (Φ := Q.Instr) (Γ := _))
  | let₂ _ _ iha ihb => exact .let₂ (by simpa only [SignatureMap.PreservesProducts.product] using iha) ihb
  | inl _ ih =>
    simpa only [LambdaSSA.Tm.mapInstr, SignatureMap.PreservesSums.coprod] using LambdaSSA.Tm.HasType.inl ih
  | inr _ ih =>
    simpa only [LambdaSSA.Tm.mapInstr, SignatureMap.PreservesSums.coprod] using LambdaSSA.Tm.HasType.inr ih
  | case _ _ _ ihe ihl ihr =>
    exact .case (by simpa only [SignatureMap.PreservesSums.coprod] using ihe) ihl ihr
  | abort _ ih => exact .abort (by simpa only [SignatureMap.PreservesSums.empty] using ih)

theorem mapRegionTyping_proof {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr}
    {L : LambdaSSA.LCtx τ} (hr : LambdaSSA.Region.HasType Γ r L) :
    LambdaSSA.Region.HasType (Γ.map g.ty) (r.mapInstr g.instr) (L.map g.ty) := by
  induction hr with
  | br hl ha => exact .br (mapContextLookup_proof g.ty hl) (mapTermTyping_proof g ha)
  | case he _ _ ihl ihr =>
    exact .case (by simpa only [SignatureMap.PreservesSums.coprod] using mapTermTyping_proof g he) ihl ihr
  | let₁ ha _ ih => exact .let₁ (mapTermTyping_proof g ha) ih
  | let₂ ha _ ih =>
    exact .let₂ (by simpa only [SignatureMap.PreservesProducts.product] using mapTermTyping_proof g ha) ih
  | cfg R _ _ ihe ihb =>
    apply LambdaSSA.Region.HasType.cfg (g.ty ∘ R)
    · simpa only [List.map_append, List.map_ofFn] using ihe
    · intro i
      simpa only [List.map_cons, List.map_append, List.map_ofFn, Function.comp_apply] using ihb i

theorem compile_mapSSASignature_proof (e : SSAEquation P) :
    compile (mapSSASignature g e) = mapCaseSignature g (compile e) := by
  rcases e with ⟨⟨n, β, A⟩, a, b⟩
  exact congrArg₂ (fun x y => (⟨⟨n, β.mapTypes g.ty, g.ty A⟩, x, y⟩ : CaseEquation Q))
    (a.toLetCase_mapSignature g) (b.toLetCase_mapSignature g)

theorem reify_mapCaseSignature_proof (e : CaseEquation P) :
    reify (mapCaseSignature g e) = mapSSASignature g (reify e) := by
  rcases e with ⟨⟨n, β, A⟩, ⟨a, da⟩, ⟨b, db⟩⟩
  exact congrArg₂ (fun x y => (⟨⟨n, β.mapTypes g.ty, g.ty A⟩, x, y⟩ : SSAEquation Q))
    (LambdaSSA.Acyclic.Code.ofLetCase_mapSignature g da)
    (LambdaSSA.Acyclic.Code.ofLetCase_mapSignature g db)

section Regions

open LambdaSSA.Semantics.Categorical (RegionTypingCoherent denoteRegion denoteRegion_spec RegionDenotes)

variable [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

theorem pullback_coherent_proof (K : CoherentRegionModel J Q) (w : RegionWitnessPullback g K) :
    letI := pullbackInstructions g K.instructions
    RegionTypingCoherent (Φ := P.Instr) J (pullbackTypes g K.types) := by
  let _ := pullbackInstructions g K.instructions
  refine ⟨?_⟩
  intro Γ r L hr a b da db
  obtain ⟨_, a', da', ea⟩ := w da
  obtain ⟨_, b', db', eb⟩ := w db
  let _ := K.instructions
  let _ := K.coherent
  have hab : a' = b' := RegionTypingCoherent.denotes_eq da' db'
  exact eq_of_heq (ea.trans (hab ▸ eb.symm))

private theorem regionDenotes_modelCongr {M N : TypeModel τ V} (hm : M = N)
    {I : InstructionModel J M P.Instr} {I' : InstructionModel J N P.Instr}
    (hi : HEq I I') {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ}
    {hr : LambdaSSA.Region.HasType Γ r L} {a : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : letI := I; RegionDenotes J M hr a) :
    ∃ b : J.obj (ctxObj N Γ) ⟶ J.obj (labelObj N L),
      (letI := I'; RegionDenotes J N hr b) ∧ HEq a b := by
  subst N
  cases eq_of_heq hi
  exact ⟨a, d, HEq.rfl⟩

private theorem regionWitness_congr {M : TypeModel κ V} [InstructionModel J M S.Instr]
    {Γ Γ' : LambdaSSA.VCtx κ} {r r' : LambdaSSA.Region S.Instr}
    {L L' : LambdaSSA.LCtx κ} (eΓ : Γ = Γ') (er : r = r') (eL : L = L')
    {α : Type} {a : α}
    (w : ∃ (hr : LambdaSSA.Region.HasType Γ r L)
      (b : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)), RegionDenotes J M hr b ∧ HEq a b) :
    ∃ (hr' : LambdaSSA.Region.HasType Γ' r' L')
      (b' : J.obj (ctxObj M Γ') ⟶ J.obj (labelObj M L')), RegionDenotes J M hr' b' ∧ HEq a b' := by
  subst Γ'
  subst r'
  subst L'
  exact w

theorem regionWitnessPullback_comp_proof (K : CoherentRegionModel J S) (wh : RegionWitnessPullback h K)
    (wg : RegionWitnessPullback g (K.pullback h (pullback_coherent_proof h K wh))) :
    RegionWitnessPullback (h.comp g) K := by
  intro Γ r L hr a da
  obtain ⟨_, d, ea⟩ := regionDenotes_modelCongr (pullbackTypes_comp_proof g h K.types)
    (pullbackInstructions_comp_proof g h K.instructions) da
  obtain ⟨_, b, db, eb⟩ := wg d
  obtain ⟨hr', c, dc, ec⟩ := wh db
  let _ := K.instructions
  exact regionWitness_congr (J := J) (M := K.types) (S := S)
    (Γ := (Γ.map g.ty).map h.ty) (r := (r.mapInstr g.instr).mapInstr h.instr)
    (L := (L.map g.ty).map h.ty) List.map_map (LambdaSSA.Region.mapInstr_comp _ _ _)
    List.map_map ⟨hr', c, dc, ea.trans (eb.trans ec)⟩

theorem regionWitnessPullback_of_thin_proof [Quiver.IsThin C] (K : CoherentRegionModel J Q) :
    RegionWitnessPullback g K := by
  intro Γ r L hr a _
  let _ := K.instructions
  let hr' := mapRegionTyping_proof g hr
  refine ⟨hr', denoteRegion J K.types hr', denoteRegion_spec J K.types hr', ?_⟩
  have he := congrArg₂ (fun G L => J.obj G ⟶ J.obj L)
    (ctxObj_pullback_proof g K.types Γ) (labelObj_pullback_proof g K.types L)
  exact (cast_heq he a).symm.trans (heq_of_eq (Subsingleton.elim _ _))

private theorem model_ext {K K' : CoherentRegionModel J P} (hm : K.types = K'.types)
    (hi : HEq K.instructions K'.instructions) : K = K' := by
  cases K
  cases K'
  cases hm
  cases eq_of_heq hi
  rfl

theorem regionWitnessPullback_primitive_proof {P Q : InstrSig τ ε} (f : P ⟶ Q)
    (K : CoherentRegionModel J Q) : RegionWitnessPullback f.toSignatureMap K := by
  intro Γ r L hr a da
  obtain ⟨b, db, eab⟩ := regionDenotes_modelCongr (pullbackTypes_primitive f K.types)
    (pullbackInstructions_primitive f K.instructions) da
  have eb := (let _ := restrictInstructions f K.instructions
              let _ := K.restrict_coherent f
              RegionDenotes.eq_denote J K.types db)
  have ec := K.denoteRegion_reduct f hr
  let _ := K.instructions
  let hr' := hr.mapInstr (InstrSig.Hom.instr f) ⟨f.source, f.target⟩
  exact regionWitness_congr (J := J) (M := K.types) (S := Q) (Γ := Γ) (L := L)
    (by simp [InstrSig.Hom.toSignatureMap]) rfl (by simp [InstrSig.Hom.toSignatureMap])
    ⟨hr', denoteRegion J K.types hr', denoteRegion_spec J K.types hr',
      eab.trans (heq_of_eq (eb.trans ec))⟩

theorem pullback_primitive_proof {P Q : InstrSig τ ε} (f : P ⟶ Q)
    (K : CoherentRegionModel J Q) (coh : letI := pullbackInstructions f.toSignatureMap K.instructions
      RegionTypingCoherent (Φ := P.Instr) J (pullbackTypes f.toSignatureMap K.types)) :
    K.pullback f.toSignatureMap coh = K.reduct f :=
  model_ext (pullbackTypes_primitive f K.types) (pullbackInstructions_primitive f K.instructions)

theorem pullback_id_proof (K : CoherentRegionModel J P)
    (coh : letI := pullbackInstructions (P := P) (Q := P) SignatureMap.id K.instructions
      RegionTypingCoherent (Φ := P.Instr) J
        (pullbackTypes (P := P) (Q := P) SignatureMap.id K.types)) :
    K.pullback (P := P) (Q := P) SignatureMap.id coh = K := by
  exact (pullback_primitive_proof (𝟙 P) K coh).trans K.reduct_id

theorem pullback_comp_proof (K : CoherentRegionModel J S)
    (cohH : letI := pullbackInstructions h K.instructions
      RegionTypingCoherent (Φ := Q.Instr) J (pullbackTypes h K.types))
    (cohG : letI := pullbackInstructions g (K.pullback h cohH).instructions
      RegionTypingCoherent (Φ := P.Instr) J (pullbackTypes g (K.pullback h cohH).types))
    (cohHG : letI := pullbackInstructions (h.comp g) K.instructions
      RegionTypingCoherent (Φ := P.Instr) J (pullbackTypes (h.comp g) K.types)) :
    K.pullback (h.comp g) cohHG = (K.pullback h cohH).pullback g cohG :=
  model_ext (pullbackTypes_comp_proof g h K.types) (pullbackInstructions_comp_proof g h K.instructions)

theorem denoteRegion_pullback_proof (K : CoherentRegionModel J Q) (w : RegionWitnessPullback g K)
    {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ}
    (hr : LambdaSSA.Region.HasType Γ r L) :
    HEq (letI := pullbackInstructions g K.instructions
         denoteRegion J (pullbackTypes g K.types) hr)
      (letI := K.instructions; denoteRegion J K.types (mapRegionTyping_proof g hr)) := by
  have d := (letI := pullbackInstructions g K.instructions
             denoteRegion_spec J (pullbackTypes g K.types) hr)
  obtain ⟨_, a', d', he⟩ := w d
  let _ := K.instructions
  let _ := K.coherent
  exact he.trans (heq_of_eq (RegionDenotes.eq_denote J K.types d'))


theorem regionWitnessPullback_iff_proof (K : CoherentRegionModel J Q) :
    RegionWitnessPullback g K ↔
      (letI := pullbackInstructions g K.instructions
       RegionTypingCoherent (Φ := P.Instr) J (pullbackTypes g K.types)) ∧
      ∀ {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ}
        (hr : LambdaSSA.Region.HasType Γ r L),
        HEq (letI := pullbackInstructions g K.instructions; denoteRegion J (pullbackTypes g K.types) hr)
          (letI := K.instructions; denoteRegion J K.types (mapRegionTyping_proof g hr)) := by
  constructor
  · intro w
    exact ⟨pullback_coherent_proof g K w, denoteRegion_pullback_proof g K w⟩
  · rintro ⟨coh, square⟩ Γ r L hr a da
    have ea := (let _ := pullbackInstructions g K.instructions
                let _ := coh
                RegionDenotes.eq_denote J (pullbackTypes g K.types) da)
    let _ := K.instructions
    let hr' := mapRegionTyping_proof g hr
    exact ⟨hr', _, denoteRegion_spec J K.types hr', (heq_of_eq ea).trans (square hr)⟩

theorem denoteSSA_pullback_proof (K : CoherentRegionModel J Q) (w : RegionWitnessPullback g K)
    {n : Nat} {β : BoundCtx τ n} {A : τ} (c : LambdaSSA.Acyclic.Code P.Instr β A) :
    HEq ((K.pullback g (pullback_coherent_proof g K w)).denoteSSA c)
      (K.denoteSSA (c.mapSignature g)) := by
  unfold CoherentRegionModel.denoteSSA
  have h := denoteRegion_pullback_proof g K w (c.toSSA_hasType (L := [A]) (exit := 0) rfl)
  have agree {Γ Γ' : LambdaSSA.VCtx υ} {r r' : LambdaSSA.Region Q.Instr}
      (eΓ : Γ = Γ') (er : r = r') {hr : LambdaSSA.Region.HasType Γ r [g.ty A]}
      {hr' : LambdaSSA.Region.HasType Γ' r' [g.ty A]} :
      letI := K.instructions
      HEq (denoteRegion J K.types hr) (denoteRegion J K.types hr') := by
    cases eΓ
    cases er
    rfl
  exact h.trans (agree (boundCtx_toList_mapTypes_proof g.ty β).symm
    (c.toSSA_mapSignature g 0).symm)

theorem ssaSat_pullback_proof (K : CoherentRegionModel J Q) (w : RegionWitnessPullback g K)
    (e : SSAEquation P) :
    let K' := K.pullback g (pullback_coherent_proof g K w)
    K.denoteSSA (mapSSASignature g e).2.1 = K.denoteSSA (mapSSASignature g e).2.2 ↔
      K'.denoteSSA e.2.1 = K'.denoteSSA e.2.2 := by
  have ha := denoteSSA_pullback_proof g K w e.2.1
  have hb := denoteSSA_pullback_proof g K w e.2.2
  constructor <;> intro he
  · exact eq_of_heq (ha.trans ((heq_of_eq he).trans hb.symm))
  · exact eq_of_heq (ha.symm.trans ((heq_of_eq he).trans hb))

variable [FreydCategory.CentralUnit J]

theorem caseSat_pullback_proof (K : CoherentRegionModel J Q) (w : RegionWitnessPullback g K)
    (e : CaseEquation P) :
    let K' := K.pullback g (pullback_coherent_proof g K w)
    ((LetCase.inst (Ctx.nil : Ctx Empty υ)).obj Q).Sat K.caseAlgebra (mapCaseSignature g e) ↔
      ((LetCase.inst (Ctx.nil : Ctx Empty τ)).obj P).Sat K'.caseAlgebra e := by
  dsimp only
  rw [← sat_reify_iff K, ← sat_reify_iff (K.pullback g (pullback_coherent_proof g K w)),
    reify_mapCaseSignature_proof]
  exact ssaSat_pullback_proof g K w (reify e)

end Regions

end Silmaril.Isotope.Institution.Acyclic

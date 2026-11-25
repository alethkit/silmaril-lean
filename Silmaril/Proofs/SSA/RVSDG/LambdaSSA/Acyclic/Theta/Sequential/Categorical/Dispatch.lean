module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Phase
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms

/-! # Relocate the flat CFG dispatcher into its two pure label phases -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Proofs

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (snd)
open Isotope.LambdaSSA.Semantics.Categorical
  (RegionDenotes Denotes labelObj labelInject ctxObj labelObjToFinite labelObjToFinite_local finiteLabelInject)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LinearChain (Site localSite externalSite)
open LinearChain.Categorical (siteArrow localInject cfgStepOf cfgStepOf_at decodeLabels decode_local decode_exit
  local_ext payload_cfg_denotes)
open Acyclic.Categorical (blockArrow blockArrow_rename blockArrow_post block_denotes)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (F : V ⥤ C) [StrongElgotFreydCategory F]
  (T : TypeModel τ V) [InstructionModel F T Φ]
variable {A B K M N H E D X Y : τ} {L : List τ}

private noncomputable abbrev Locals {n : Nat} (R : Fin n → τ) := labelObj T (List.ofFn R)

private noncomputable def localDesc {n : Nat} (R : Fin n → τ) {O : V}
    (legs : ∀ i, T.obj (R i) ⟶ O) : Locals T R ⟶ O :=
  labelObjToFinite T R ≫ Limits.Sigma.desc legs

omit [SymmetricCategory V] [DistributiveTensor V] in
@[reassoc] private theorem local_desc {n : Nat} (R : Fin n → τ) {O : V}
    (legs : ∀ i, T.obj (R i) ⟶ O) (i : Fin n) :
    localInject T R i ≫ localDesc T R legs = legs i := by
  rw [localDesc, ← Category.assoc]
  change (labelInject T i _ ≫ labelObjToFinite T R) ≫ Limits.Sigma.desc legs = _
  rw [labelObjToFinite_local, finiteLabelInject, Limits.Sigma.ι_comp_desc]

private noncomputable def rawArrow (b : Block Φ L X) :
    F.obj (T.obj X) ⟶ F.obj (labelObj T L) :=
  blockArrow F T (fun _ p => F.map (siteArrow T p)) b

private noncomputable def step {n : Nat} (R : Fin n → τ) (L : List τ)
    (blocks : ∀ i, Block Φ (List.ofFn R ++ L) (R i)) :
    F.obj (Locals T R) ⟶ F.obj (labelObj T L) ⨿ F.obj (Locals T R) :=
  cfgStepOf F T R L (fun i => rawArrow F T (blocks i))

private noncomputable def routing {n : Nat} (R : Fin n → τ) (L : List τ)
    {O : C} (next : F.obj (labelObj T L) ⨿ F.obj (Locals T R) ⟶ O)
    {Z : τ} (p : Site (List.ofFn R ++ L) Z) : F.obj (T.obj Z) ⟶ O :=
  F.map (siteArrow T p) ≫ decodeLabels F T R L ≫ next

@[reassoc] private theorem step_at {n : Nat} (R : Fin n → τ) (L : List τ)
    (blocks : ∀ i, Block Φ (List.ofFn R ++ L) (R i)) (i : Fin n) {O : C}
    (next : F.obj (labelObj T L) ⨿ F.obj (Locals T R) ⟶ O) :
    F.map (localInject T R i) ≫ step F T R L blocks ≫ next =
      blockArrow F T (fun _ p => routing F T R L next p) (blocks i) := by
  rw [← Category.assoc, step, cfgStepOf_at, Category.assoc, rawArrow, blockArrow_post]
  rfl

private theorem cast_arrow {O : C} (arrows : Acyclic.Categorical.LabelArrows F T L O)
    (eq : X = Y) (b : Block Φ L X) :
    blockArrow F T arrows (eq ▸ b) =
      F.map (eqToHom (congrArg T.obj eq.symm)) ≫ blockArrow F T arrows b := by
  cases eq
  simp

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem cast_site (eq : X = Y) (p : Site L X) :
    siteArrow T (eq ▸ p) = eqToHom (congrArg T.obj eq.symm) ≫ siteArrow T p := by
  cases eq
  simp

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem merge_exit (M : τ) (i : Fin 2)
    (typed : Isotope.SSA.At ([M,M] : List τ) i M) :
    labelInject T i typed ≫ mergeLabels T M = 𝟙 _ := by
  revert typed
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => j.elim0) j) i
  · intro typed
    simp [labelInject, mergeLabels]
  · intro typed
    simp [labelInject, mergeLabels]
    rfl

variable (s : Loops Φ A B K M N H E D)

local notation "R₁" => Theta.localTypes s.first
local notation "R₂" => Theta.localTypes s.second
local notation "R" => Sequential.localTypes s
local notation "P" => labelObj T [M,M]
local notation "O" => labelObj T [E,D]
local notation "X₁" => Locals T R₁
local notation "X₂" => Locals T R₂

private noncomputable def phases : Locals T R ⟶ X₁ ⨿ X₂ :=
  localDesc T R (Fin.addCases (motive := fun i => T.obj (R i) ⟶ X₁ ⨿ X₂)
    (fun i => eqToHom (congrArg T.obj (first_type s i)) ≫ localInject T R₁ i ≫ coprod.inl)
    (fun i => eqToHom (congrArg T.obj (second_type s i)) ≫ localInject T R₂ i ≫ coprod.inr))

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem phases_left (i : Fin (firstCount s)) :
    localInject T R (i.castAdd (secondCount s)) ≫ phases T s =
      eqToHom (congrArg T.obj (first_type s i)) ≫ localInject T R₁ i ≫ coprod.inl := by
  rw [phases, local_desc]
  exact Fin.addCases_left i

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem phases_right (i : Fin (secondCount s)) :
    localInject T R (i.natAdd (firstCount s)) ≫ phases T s =
      eqToHom (congrArg T.obj (second_type s i)) ≫ localInject T R₂ i ≫ coprod.inr := by
  rw [phases, local_desc]
  exact Fin.addCases_right i

private noncomputable def firstStep := step F T R₁ [M,M] (Theta.blockAt s.first)
private noncomputable def secondStep := step F T R₂ [E,D] (Theta.blockAt s.second)
private noncomputable def flatStep := step F T R [E,D] (blockAt s)
private noncomputable def enterSecond := mergeLabels T M ≫ localInject T R₂ 0
private noncomputable def move := coprod.map (𝟙 (F.obj O)) (F.map (phases T s))
private noncomputable def closeFirst : F.obj P ⨿ F.obj X₁ ⟶ F.obj O ⨿ F.obj (X₁ ⨿ X₂) :=
  coprod.desc (F.map (enterSecond T s) ≫ F.map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫ coprod.inr)
    (F.map (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ≫ coprod.inr)
private noncomputable def closeSecond : F.obj O ⨿ F.obj X₂ ⟶ F.obj O ⨿ F.obj (X₁ ⨿ X₂) :=
  coprod.map (𝟙 (F.obj O)) (F.map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂))

private theorem routing_local {n : Nat} (family : Fin n → τ) (L : List τ) (i : Fin n) {U : C}
    (next : F.obj (labelObj T L) ⨿ F.obj (Locals T family) ⟶ U) :
    routing F T family L next (localSite family L i) = F.map (localInject T family i) ≫ coprod.inr ≫ next := by
  rw [routing, ← Category.assoc, decode_local, Category.assoc]

private theorem routing_exit {n : Nat} (family : Fin n → τ) (L : List τ) (i : Fin L.length) {U : C}
    (next : F.obj (labelObj T L) ⨿ F.obj (Locals T family) ⟶ U)
    (lookup : Isotope.SSA.At L i (L.get i)) :
    routing F T family L next (externalSite family L i) = F.map (labelInject T i lookup) ≫ coprod.inl ≫ next := by
  rw [routing, ← Category.assoc, decode_exit F T family L i lookup, Category.assoc]

private theorem routing_cast {n : Nat} (family : Fin n → τ) (L : List τ) {U : C}
    (next : F.obj (labelObj T L) ⨿ F.obj (Locals T family) ⟶ U) (h : X = Y)
    (p : Site (List.ofFn family ++ L) X) :
    routing F T family L next (h ▸ p) = F.map (eqToHom (congrArg T.obj h.symm)) ≫ routing F T family L next p := by
  rw [routing, cast_site, F.map_comp, Category.assoc]
  rfl

omit [InstructionModel F T Φ] in
private theorem route_firstLocal (i : Fin (firstCount s)) :
    routing F T R [E,D] (move F T s) (firstLocal s i) =
      F.map (localInject T R₁ i) ≫ F.map (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ≫ coprod.inr := by
  have route : eqToHom (congrArg T.obj (first_type s i).symm) ≫
      localInject T R (i.castAdd (secondCount s)) ≫ phases T s =
        localInject T R₁ i ≫ (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) := by
    rw [phases_left, eqToHom_trans_assoc]
    simp
  rw [firstLocal, routing_cast, routing_local, move, coprod.inr_map]
  simpa only [F.map_comp, Category.assoc] using
    congrArg (fun f => F.map f ≫ (coprod.inr : F.obj (X₁ ⨿ X₂) ⟶ F.obj O ⨿ F.obj (X₁ ⨿ X₂))) route

omit [InstructionModel F T Φ] in
private theorem route_secondLocal (i : Fin (secondCount s)) :
    routing F T R [E,D] (move F T s) (secondLocal s i) =
      F.map (localInject T R₂ i) ≫ F.map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫ coprod.inr := by
  have route : eqToHom (congrArg T.obj (second_type s i).symm) ≫
      localInject T R (i.natAdd (firstCount s)) ≫ phases T s =
        localInject T R₂ i ≫ (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) := by
    rw [phases_right, eqToHom_trans_assoc]
    simp
  rw [secondLocal, routing_cast, routing_local, move, coprod.inr_map]
  simpa only [F.map_comp, Category.assoc] using
    congrArg (fun f => F.map f ≫ (coprod.inr : F.obj (X₁ ⨿ X₂) ⟶ F.obj O ⨿ F.obj (X₁ ⨿ X₂))) route

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem enter_exit (i : Fin 2) (typed : Isotope.SSA.At ([M,M] : List τ) i M) :
    labelInject T i typed ≫ enterSecond T s = localInject T R₂ 0 := by
  unfold enterSecond
  rw [← Category.assoc, merge_exit T M i typed, Category.id_comp]

omit [InstructionModel F T Φ] in
private theorem route_left (p : Site (Theta.Labels s.first) X) :
    routing F T R [E,D] (move F T s) (leftSite s p) =
      routing F T R₁ [M,M] (closeFirst F T s) p := by
  unfold leftSite redirect
  generalize eq : splitSite R₁ [M,M] p = split
  obtain ⟨dest, site⟩ := split
  subst p
  cases dest with
  | «local» i =>
    change routing F T R [E,D] (move F T s) (firstLocal s i) =
      routing F T R₁ [M,M] (closeFirst F T s) (localSite _ _ i)
    rw [route_firstLocal, routing_local, closeFirst, coprod.inr_desc]
  | external i =>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => j.elim0) j) i
    · change routing F T R [E,D] (move F T s) (secondLocal s 0) =
        routing F T R₁ [M,M] (closeFirst F T s) (externalSite R₁ [M,M] 0)
      rw [route_secondLocal, routing_exit F T R₁ [M,M] 0 _ rfl, closeFirst, coprod.inl_desc]
      simpa only [F.map_comp, Category.assoc] using
        congrArg (fun f => F.map f ≫ F.map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫
          (coprod.inr : F.obj (X₁ ⨿ X₂) ⟶ F.obj O ⨿ F.obj (X₁ ⨿ X₂))) (enter_exit T s 0 rfl).symm
    · change routing F T R [E,D] (move F T s) (secondLocal s 0) =
        routing F T R₁ [M,M] (closeFirst F T s) (externalSite R₁ [M,M] 1)
      rw [route_secondLocal, routing_exit F T R₁ [M,M] 1 _ rfl, closeFirst, coprod.inl_desc]
      simpa only [F.map_comp, Category.assoc] using
        congrArg (fun f => F.map f ≫ F.map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫
          (coprod.inr : F.obj (X₁ ⨿ X₂) ⟶ F.obj O ⨿ F.obj (X₁ ⨿ X₂))) (enter_exit T s 1 rfl).symm

omit [InstructionModel F T Φ] in
private theorem route_right (p : Site (Theta.Labels s.second) X) :
    routing F T R [E,D] (move F T s) (rightSite s p) =
      routing F T R₂ [E,D] (closeSecond F T s) p := by
  unfold rightSite redirect
  generalize eq : splitSite R₂ [E,D] p = split
  obtain ⟨dest, site⟩ := split
  subst p
  cases dest with
  | «local» i =>
    change routing F T R [E,D] (move F T s) (secondLocal s i) =
      routing F T R₂ [E,D] (closeSecond F T s) (localSite _ _ i)
    rw [route_secondLocal, routing_local, closeSecond, coprod.inr_map]
  | external i =>
    change routing F T R [E,D] (move F T s) (externalSite _ _ i) =
      routing F T R₂ [E,D] (closeSecond F T s) (externalSite _ _ i)
    have h := List.getElem?_eq_getElem i.isLt
    rw [routing_exit F T R [E,D] i _ h, routing_exit F T R₂ [E,D] i _ h,
      move, closeSecond, coprod.inl_map, coprod.inl_map]

private theorem dispatch_square :
    flatStep F T s ≫ move F T s =
      F.map (phases T s) ≫ phaseStep F (firstStep F T s) (secondStep F T s) (F.map (enterSecond T s)) := by
  apply local_ext F T R
  intro i
  refine Fin.addCases (motive := fun j =>
    F.map (localInject T R j) ≫ flatStep F T s ≫ move F T s =
      F.map (localInject T R j) ≫ F.map (phases T s) ≫
        phaseStep F (firstStep F T s) (secondStep F T s) (F.map (enterSecond T s))) ?_ ?_ i
  · intro i
    rw [← Category.assoc (F.map (localInject T R _)) (F.map (phases T s)), ← F.map_comp, phases_left]
    simp only [F.map_comp, Category.assoc, phase_inl]
    change F.map (localInject T R _) ≫ step F T R [E,D] (blockAt s) ≫ _ =
      _ ≫ (F.map (localInject T R₁ i) ≫ firstStep F T s ≫ closeFirst F T s)
    rw [step_at, firstStep, step_at]
    simp only [blockAt, Fin.addCases_left, cast_arrow]
    apply congrArg (fun arrow => F.map (eqToHom (congrArg T.obj (first_type s i))) ≫ arrow)
    rw [blockArrow_rename]
    congr 1
    funext Z p
    exact route_left F T s p
  · intro i
    rw [← Category.assoc (F.map (localInject T R _)) (F.map (phases T s)), ← F.map_comp, phases_right]
    simp only [F.map_comp, Category.assoc, phase_inr]
    change F.map (localInject T R _) ≫ step F T R [E,D] (blockAt s) ≫ _ =
      _ ≫ (F.map (localInject T R₂ i) ≫ secondStep F T s ≫ closeSecond F T s)
    rw [step_at, secondStep, step_at]
    simp only [blockAt, Fin.addCases_right, cast_arrow]
    apply congrArg (fun arrow => F.map (eqToHom (congrArg T.obj (second_type s i))) ≫ arrow)
    rw [blockArrow_rename]
    congr 1
    funext Z p
    exact route_right F T s p

private theorem factor :
    F.map (localInject T R 0) ≫ iterate (flatStep F T s) =
      iterate (Theta.Categorical.activation F T s.first) ≫ F.map (mergeLabels T M) ≫
        iterate (Theta.Categorical.activation F T s.second) := by
  let phased := phaseStep F (firstStep F T s) (secondStep F T s) (F.map (enterSecond T s))
  have uniform : iterate (flatStep F T s) = F.map (phases T s) ≫ iterate phased :=
    ElgotFreydCategory.pure_uniformity F _ phased (phases T s) (dispatch_square F T s)
  have start : localInject T R 0 ≫ phases T s =
      localInject T R₁ 0 ≫ (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) := by
    have h := phases_left T s (0 : Fin (firstCount s))
    change localInject T R 0 ≫ phases T s = _ at h
    simpa using h
  rw [uniform, ← F.map_comp_assoc, start, F.map_comp, Category.assoc, iterate_phases, ← Category.assoc]
  have leftFold : F.map (localInject T R₁ 0) ≫ iterate (firstStep F T s) = _ :=
    Theta.Categorical.dispatcher_at_header F T s.first
  rw [leftFold]
  rw [enterSecond, F.map_comp]
  simp only [Category.assoc]
  have rightFold : F.map (localInject T R₂ 0) ≫ iterate (secondStep F T s) = _ :=
    Theta.Categorical.dispatcher_at_header F T s.second
  rw [rightFold]

variable [FreydCategory.CentralUnit F]

theorem region_denotes : RegionDenotes F T (regionTyping s) (denote F T s) := by
  let proj := F.map (snd (ctxObj T []) (T.obj A))
  have db (i) : RegionDenotes F T ((blockAt s i).typing [A])
      (F.map (snd (ctxObj T [A]) (T.obj (R i))) ≫ rawArrow F T (blockAt s i)) :=
    block_denotes F T _ _
  have d := payload_cfg_denotes F T R 0
    (.br (localSite R [E,D] 0).typing (.var rfl)) (fun i => (blockAt s i).typing [A]) proj
    (RegionDenotes.br (h := (localSite R [E,D] 0).typing) (Denotes.var (i := 0) rfl))
    (fun i => rawArrow F T (blockAt s i)) db
  change RegionDenotes F T (regionTyping s) (proj ≫ F.map (localInject T R 0) ≫ iterate (flatStep F T s)) at d
  rw [factor F T s] at d
  have handoff : handoffContext T M ≫ snd (ctxObj T []) (T.obj M) = mergeLabels T M :=
    CartesianMonoidalCategory.lift_snd _ _
  unfold denote Theta.Categorical.denoteLoop Theta.Categorical.denote
  simp only [Category.assoc, ← F.map_comp_assoc, handoff]
  exact d

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Proofs

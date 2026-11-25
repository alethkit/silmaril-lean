module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Proofs

open CategoryTheory
open OrderedRuntime.Structured (Values Ty)
open OrderedState.Partial (Abnormal Path interpretation runOpen runNode Restart loopAbnormal kindAbnormal abnormalAt)

universe u v w
variable {V : Type u} {A B C : Signature.{u,v} V} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (f : A ⟶ B) (m : Model.{u,v,w} B σ)

local notation "rename" => Institution.Signature.opcodeMap (Signature.Hom.forget f)

private theorem denote_map (t : Term A.base.op args past sigs outs)
    (input : Tuple (Values m.value) args) (locals : Locals (Values m.value) past) :
    (Institution.mapTerm rename t).denoteOpenWith (interpretation m) input locals =
      t.denoteOpenWith (interpretation (reduct f m)) input locals := by
  rw [Institution.denoteOpen_map]
  unfold Institution.monadicReduct
  refine congrArg (fun
      (primitive : ∀ {i o : Ports (Ty V)}, A.base.op i o → Tuple (Values m.value) i →
        StateT σ _root_.Part (Tuple (Values m.value) o)) =>
    show StateT σ _root_.Part (Tuple (Values m.value) outs) from
      t.denoteOpenWith (⟨m.value, fun _ => PUnit, primitive⟩ :
        MonadicModel.{u,v,max u w} A.base.op (StateT σ _root_.Part)) input locals) ?_
  funext ins outs op values
  cases op <;> rfl

private theorem runOpen_map (t : Term A.base.op args past sigs outs)
    (input : Tuple (Values m.value) args) (locals : Locals (Values m.value) past) (store : σ) :
    runOpen m (Institution.mapTerm rename t) input locals store =
      runOpen (reduct f m) t input locals store := by
  simp only [runOpen, denote_map]

theorem observe_map (g : Graph A.base.op args [] sigs outs)
    (input : Tuple (Values m.value) args) (store : σ) :
    OrderedState.Partial.observe m (Institution.mapGraph rename g) input store =
      OrderedState.Partial.observe (reduct f m) g input store := by
  simp only [OrderedState.Partial.observe, Institution.mapGraph, Term.toTerm_toGraph, runOpen_map]

variable {value : V → Type (max u w)}

private abbrev Image (f : A ⟶ B) (p : Abnormal A.base.effect value σ → Prop)
    (target : Abnormal B.base.effect value σ) : Prop :=
  ∃ source, p source ∧ mapAbnormal f source = target

private theorem prefix_image {f : A ⟶ B} {target : Abnormal B.base.effect value σ}
    {X : Type (max u w)} {ok : _root_.Part X}
    {first : Abnormal A.base.effect value σ → Prop}
    {rest : X → Abnormal A.base.effect value σ → Prop} :
    Image f first target ∨ (∃ x ∈ ok, Image f (rest x) target) ↔
      Image f (fun obs => first obs ∨ ∃ x ∈ ok, rest x obs) target := by
  constructor
  · rintro (⟨source, blocked, rfl⟩ | ⟨x, ran, source, blocked, rfl⟩)
    · exact ⟨source, .inl blocked, rfl⟩
    · exact ⟨source, .inr ⟨x, ran, blocked⟩, rfl⟩
  · rintro ⟨source, blocked | ⟨x, ran, blocked⟩, rfl⟩
    · exact .inl ⟨source, blocked, rfl⟩
    · exact .inr ⟨x, ran, source, blocked, rfl⟩

private theorem effect_image {f : A ⟶ B} {target : Abnormal B.base.effect value σ}
    {source : Abnormal A.base.effect value σ} {p : Prop} :
    (p ∧ target = mapAbnormal f source) ↔ Image f (fun obs => p ∧ obs = source) target := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨source, ⟨h, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨h, rfl⟩

private theorem loop_image (f : A ⟶ B) (m : Model.{u,v,w} B σ)
    {X : Type (max u w)} (restart : X → X → Prop) (x : X)
    {child : X → Abnormal A.base.effect m.value σ → Prop}
    {child' : X → Abnormal B.base.effect m.value σ → Prop}
    {target : Abnormal B.base.effect m.value σ}
    (child_map : ∀ y, child' y target ↔ Image f (child y) target) :
    loopAbnormal m restart child' x target ↔
      Image f (loopAbnormal (reduct f m) restart child x) target := by
  constructor
  · rintro (⟨y, ran, bad⟩ | ⟨rfl, inf⟩)
    · obtain ⟨source, endpoint, rfl⟩ := (child_map y).mp bad
      exact ⟨source, .inl ⟨y, ran, endpoint⟩, rfl⟩
    · exact ⟨.diverges, .inr ⟨rfl, inf⟩, rfl⟩
  · rintro ⟨source, ⟨y, ran, bad⟩ | ⟨rfl, inf⟩, rfl⟩
    · exact .inl ⟨y, ran, (child_map y).mpr ⟨source, bad, rfl⟩⟩
    · exact .inr ⟨rfl, inf⟩

theorem abnormalAt_map (t : Term A.base.op args past sigs outs) (path : Path)
    (input : Tuple (Values m.value) args) (locals : Locals (Values m.value) past) (store : σ)
    (target : Abnormal B.base.effect m.value σ) :
    abnormalAt m path (Institution.mapTerm rename t) input locals store target ↔
      ∃ source, abnormalAt (reduct f m) path t input locals store source ∧
        mapAbnormal f source = target := by
  induction t generalizing path store with
  | ret => simp only [Institution.mapTerm, abnormalAt, false_and, exists_false]
  | bind node children rest ihChild ihRest =>
    obtain ⟨ins, kind, wires, childSigs⟩ := node
    cases kind with
    | base shape =>
      cases shape with
      | simple op =>
        cases op with
        | pure op =>
          simp only [Institution.mapTerm, abnormalAt, kindAbnormal, runNode, Kind.denoteWith,
            interpretation, OrderedRuntime.Structured.Model.step, Institution.Signature.opcodeMap, reduct]
          refine (or_congr ?_ (exists_congr fun x => and_congr_right fun _ => ihRest ..)).trans prefix_image
          exact ⟨False.elim, fun ⟨_, impossible, _⟩ => impossible⟩
        | effect op =>
          simp only [Institution.mapTerm, abnormalAt, kindAbnormal, runNode, Kind.denoteWith,
            interpretation, OrderedRuntime.Structured.Model.step, Institution.Signature.opcodeMap, reduct]
          exact (or_congr (effect_image (f := f) (source :=
              .blocked ⟨path, _, _, _, op, wires.read input locals, store⟩))
            (exists_congr fun x => and_congr_right fun _ => ihRest ..)).trans prefix_image
      | gamma =>
        simp only [Institution.mapTerm, abnormalAt, runNode, Kind.denoteWith, denote_map]
        generalize wires.read input locals = selected
        cases selected with
        | cons tag payload =>
          exact (or_congr (ihChild tag.down (path ++ [(_, tag.down.val)]) payload PUnit.unit store)
            (exists_congr fun x => and_congr_right fun _ => ihRest ..)).trans prefix_image
    | theta =>
      simp only [Institution.mapTerm, abnormalAt, kindAbnormal, runNode, Kind.denoteWith,
        runOpen_map, denote_map]
      exact (or_congr (loop_image f m _ _ (fun _ => ihChild ..))
        (exists_congr fun x => and_congr_right fun _ => ihRest ..)).trans prefix_image

theorem abnormal_map (g : Graph A.base.op args [] sigs outs)
    (input : Tuple (Values m.value) args) (store : σ)
    (target : Abnormal B.base.effect m.value σ) :
    OrderedState.Partial.abnormal m (Institution.mapGraph rename g) input store target ↔
      ∃ source, OrderedState.Partial.abnormal (reduct f m) g input store source ∧
        mapAbnormal f source = target := by
  simp only [OrderedState.Partial.abnormal, Institution.mapGraph, Term.toTerm_toGraph, abnormalAt_map]

private theorem mapBlock_injective (f : A ⟶ B) :
    Function.Injective (mapBlock (σ := σ) (value := value) f) := by
  rintro ⟨path, vertex, ins, outs, opcode, input, store⟩
    ⟨path', vertex', ins', outs', opcode', input', store'⟩ mapped
  simp only [mapBlock] at mapped
  injection mapped with path_eq vertex_eq ins_eq outs_eq opcode_eq input_eq store_eq
  subst path' vertex' ins' outs' store'
  have eq := (Signature.Hom.effect_injective f ins outs) (eq_of_heq opcode_eq)
  subst opcode'
  cases eq_of_heq input_eq
  rfl

theorem mapAbnormal_injective (f : A ⟶ B) :
    Function.Injective (mapAbnormal (σ := σ) (value := value) f) := by
  intro x y eq
  cases x <;> cases y <;> simp only [mapAbnormal, Abnormal.blocked.injEq,
    reduceCtorEq] at *
  exact mapBlock_injective f eq

theorem abnormal_map_iff (f : A ⟶ B) (m : Model.{u,v,w} B σ)
    (g : Graph A.base.op args [] sigs outs) (input : Tuple (Values m.value) args) (store : σ)
    (source : Abnormal A.base.effect m.value σ) :
    OrderedState.Partial.abnormal m (Institution.mapGraph (Signature.Hom.opcodeMap f) g) input store (mapAbnormal f source) ↔
      OrderedState.Partial.abnormal (reduct f m) g input store source := by
  constructor
  · intro observed
    obtain ⟨other, ran, eq⟩ := (abnormal_map f m g input store _).mp observed
    exact (mapAbnormal_injective f eq) ▸ ran
  · intro ran
    exact (abnormal_map f m g input store _).mpr ⟨source, ran, rfl⟩

theorem satisfaction (f : A ⟶ B) (e : Equation A) (m : Model.{u,v,w} B σ) :
    Equation.Holds (Equation.map f e) m ↔ Equation.Holds e (reduct f m) := by
  simp only [Equation.Holds, Equation.map, Institution.Equation.map, observe_map, abnormal_map]
  constructor
  · intro h input store
    obtain ⟨returns, abnormal⟩ := h input store
    refine ⟨returns, fun obs => ?_⟩
    simpa only [((mapAbnormal_injective f).eq_iff), exists_eq_right] using abnormal (mapAbnormal f obs)
  · intro h input store
    obtain ⟨returns, abnormal⟩ := h input store
    exact ⟨returns, fun target => exists_congr fun source => and_congr_left' (abnormal source)⟩

theorem reductFunctor_id (A : Signature.{u,v} V) :
    reductFunctor (σ := σ) (𝟙 A) = 𝟭 (Discrete (Model A σ)) :=
  CategoryTheory.Functor.ext (fun m => by cases m; rfl)

theorem reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (σ := σ) (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  apply Discrete.functor_ext
  intro model
  rfl

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Proofs

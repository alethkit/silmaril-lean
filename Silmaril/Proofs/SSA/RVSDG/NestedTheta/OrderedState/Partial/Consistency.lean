module

public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Thms
public import Silmaril.Semantics.ElgotMonads.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Proofs

open OrderedRuntime.Structured (Instruction Values Ty)
open Silmaril.Elgot (iter)

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args ins outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem mem_theta {value : V → Type (max u w)}
    (body : Tuple (Values value) ins →
      StateT σ _root_.Part (Tuple (Values value) (Theta.BodyResults ins)))
    (input output : Configuration value σ ins) :
    output ∈ (iter (stepWith body) input.1).run input.2 ↔
      Theta.Iterate (fun x again y => tagged again y ∈ (body x.1).run x.2) input output := by
  rw [Silmaril.Elgot.StateT.run_iter]
  change output ∈ iter (Silmaril.Elgot.StateT.body (stepWith body)) input ↔ _
  rw [Silmaril.Elgot.Part.mem_iter_iff]
  constructor
  · intro h
    induction h with
    | done last => exact .stop ((mem_routedStep body _ _ false).mp last)
    | more next _ ih => exact .again ((mem_routedStep body _ _ true).mp next) ih
  · intro h
    induction h with
    | stop last => exact .done ((mem_routedStep body _ _ false).mpr last)
    | again next _ ih => exact .more ((mem_routedStep body _ _ true).mpr next) ih

private structure Classified {X A : Type*} (res : _root_.Part X) (abnormal : A → Prop) : Prop where
  disjoint : ∀ x ∈ res, ∀ a, ¬ abnormal a
  unique : ∀ a b, abnormal a → abnormal b → a = b
  exists_endpoint : res.Dom ∨ ∃ a, abnormal a

private theorem Classified.bind {X Y A : Type*} {res : _root_.Part X} {next : X → _root_.Part Y}
    {bad : A → Prop} {later : X → A → Prop} (first : Classified res bad)
    (rest : ∀ x, Classified (next x) (later x)) :
    Classified (res.bind next) (fun a => bad a ∨ ∃ x ∈ res, later x a) := by
  constructor
  · intro y hy a ha
    obtain ⟨x, hx, got⟩ := _root_.Part.mem_bind_iff.mp hy
    rcases ha with early | ⟨x', hx', late⟩
    · exact first.disjoint x hx a early
    · cases _root_.Part.mem_unique hx hx'
      exact (rest x).disjoint y got a late
  · intro a b ha hb
    rcases ha with early | ⟨x, hx, late⟩ <;> rcases hb with early' | ⟨x', hx', late'⟩
    · exact first.unique a b early early'
    · exact (first.disjoint x' hx' a early).elim
    · exact (first.disjoint x hx b early').elim
    · cases _root_.Part.mem_unique hx hx'
      exact (rest x).unique a b late late'

  · obtain defined | ⟨a, early⟩ := first.exists_endpoint
    · have ran := _root_.Part.get_mem defined
      obtain returned | ⟨a, late⟩ := (rest (res.get defined)).exists_endpoint
      · exact .inl ⟨defined, returned⟩
      · exact .inr ⟨a, .inr ⟨_, ran, late⟩⟩
    · exact .inr ⟨a, .inl early⟩

private theorem iterate_of_reached {X : Type*} {step : X → Bool → X → Prop}
    {start finish output : X} (ran : Relation.ReflTransGen (fun x y => step x true y) start finish)
    (last : step finish false output) : Theta.Iterate step start output := by
  induction ran using Relation.ReflTransGen.head_induction_on with
  | refl => exact .stop last
  | head step _ ih => exact .again step ih

private theorem tagged_cases {value : V → Type (max u w)}
    (result : Configuration value σ (Theta.BodyResults ins)) :
    ∃ y, result = tagged false y ∨ result = tagged true y := by
  obtain ⟨tuple, store⟩ := result
  cases tuple with
  | cons selector payload =>
    obtain ⟨tag⟩ := selector
    refine ⟨(payload, store), ?_⟩
    revert tag
    exact Fin.cases (.inl rfl) (Fin.cases (.inr rfl) (fun i => i.elim0))

private theorem reached_unique {X : Type*} {R : X → X → Prop}
    (unique : ∀ x a b, R x a → R x b → a = b) {x y z : X}
    (left : Relation.ReflTransGen R x y) (right : Relation.ReflTransGen R x z)
    (stopL : ∀ a, ¬ R y a) (stopR : ∀ a, ¬ R z a) : y = z := by
  induction left using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain rfl | ⟨_, step, _⟩ := right.cases_head
    · rfl
    · exact (stopL _ step).elim
  | head step _ ih =>
    obtain rfl | ⟨_, other, tail⟩ := right.cases_head
    · exact (stopR _ step).elim
    · cases unique _ _ _ step other
      exact ih tail

private theorem trace_reached {X : Type*} {R : X → X → Prop}
    (unique : ∀ x a b, R x a → R x b → a = b) {x y : X}
    (ran : Relation.ReflTransGen R x y) (inf : InfiniteTrace R x) : InfiniteTrace R y := by
  induction ran with
  | refl => exact inf
  | tail _ step ih =>
    obtain ⟨_, other, tail⟩ := ih.unfold
    cases unique _ _ _ step other
    exact tail

private theorem theta_consistent (m : Model.{u,v,w} P E σ)
    (body : Tuple (Values m.value) ins →
      StateT σ _root_.Part (Tuple (Values m.value) (Theta.BodyResults ins)))
    (bad : Configuration m.value σ ins → Abnormal E m.value σ → Prop)
    (child : ∀ x, Classified ((body x.1).run x.2) (bad x))
    (start : Configuration m.value σ ins) :
    Classified ((iter (stepWith body) start.1).run start.2)
      (loopAbnormal m (Restart m fun x => (body x.1).run x.2) bad start) := by
  let restart := Restart m fun x => (body x.1).run x.2
  have unique : ∀ x a b, restart x a → restart x b → a = b := by
    intro x a b left right
    have tagged_eq := _root_.Part.mem_unique left right
    cases a with
    | mk payload store =>
      cases b with
      | mk other otherStore =>
        simp only [tagged, Prod.mk.injEq, Tuple.cons.injEq] at tagged_eq
        exact Prod.ext tagged_eq.1.2 tagged_eq.2
  have badStops : ∀ x a, bad x a → ∀ y, ¬ restart x y := by
    intro x a h y next
    exact (child x).disjoint (tagged true y) next a h
  have noTrace : ∀ x a, bad x a → Relation.ReflTransGen restart start x →
      InfiniteTrace restart start → False := by
    intro x a h ran inf
    obtain ⟨y, next, _⟩ := (trace_reached unique ran inf).unfold
    exact badStops x a h y next
  constructor
  · intro output member obs
    obtain loop := (mem_theta body start output).mp member
    have stops : ∃ x, Relation.ReflTransGen restart start x ∧
        tagged false output ∈ (body x.1).run x.2 := by
      clear member noTrace
      induction loop with
      | stop done => exact ⟨_, .refl, done⟩
      | again next _ ih =>
        obtain ⟨x, ran, last⟩ := ih
        exact ⟨x, ran.head next, last⟩
    obtain ⟨x, ran, last⟩ := stops
    have stop : ∀ y, ¬ restart x y := by
      intro y next
      have tags := congrArg (fun result : Configuration m.value σ (Theta.BodyResults ins) =>
        (result.1.get .head).down.val) (_root_.Part.mem_unique last next)
      exact Nat.zero_ne_one tags
    rintro (⟨y, steps, bad⟩ | ⟨_, inf⟩)
    · cases reached_unique unique ran steps stop (badStops _ _ bad)
      exact (child x).disjoint _ last obs bad
    · obtain ⟨_, next, _⟩ := (trace_reached unique ran inf).unfold
      exact stop _ next
  · intro a b obs obs'
    rcases obs with ⟨x, ran, h⟩ | ⟨rfl, inf⟩ <;> rcases obs' with ⟨y, ran', h'⟩ | ⟨rfl, inf'⟩
    · cases reached_unique unique ran ran' (badStops _ _ h) (badStops _ _ h')
      exact (child x).unique a b h h'
    · exact (noTrace _ _ h ran inf').elim
    · exact (noTrace _ _ h' ran' inf).elim
    · rfl

  · classical
    by_cases returned : ((iter (stepWith body) start.1).run start.2).Dom
    · exact .inl returned
    right
    by_cases ended : ∃ x, Relation.ReflTransGen restart start x ∧ ∃ a, bad x a
    · obtain ⟨x, ran, a, observed⟩ := ended
      exact ⟨a, .inl ⟨x, ran, observed⟩⟩
    refine ⟨.diverges, .inr ⟨rfl, ?_⟩⟩
    apply InfiniteTrace.coinduct (Relation.ReflTransGen restart start) ?_ .refl
    intro x ran
    obtain completed | abnormal := (child x).exists_endpoint
    · obtain ⟨y, equality⟩ := tagged_cases (((body x.1).run x.2).get completed)
      have member := _root_.Part.get_mem completed
      rcases equality with stop | next
      · rw [stop] at member
        exact (returned ((mem_theta body start y).mpr (iterate_of_reached ran member)).1).elim
      · rw [next] at member
        exact ⟨y, member, ran.tail member⟩
    · exact (ended ⟨x, ran, abnormal⟩).elim

private theorem kind_consistent (m : Model.{u,v,w} P E σ)
    (kind : Kind (Instruction P E) ins outs) (path : Path) (vertex : Nat)
    (body : Fin kind.arity → Tuple (Values m.value) kind.entry →
      StateT σ _root_.Part (Tuple (Values m.value) kind.exit))
    (bad : Fin kind.arity → Configuration m.value σ kind.entry → Abnormal E m.value σ → Prop)
    (child : ∀ j x, Classified ((body j x.1).run x.2) (bad j x))
    (input : Configuration m.value σ ins) :
    Classified ((kind.denoteWith (interpretation m) body input.1).run input.2)
      (kindAbnormal m path vertex kind (fun j x => (body j x.1).run x.2) bad input) := by
  cases kind with
  | base shape =>
    cases shape with
    | simple op =>
      obtain ⟨input, store⟩ := input
      cases op with
      | pure =>
        exact ⟨fun _ _ _ h => h, fun _ _ h _ => h.elim, .inl (_root_.Part.some_dom _)⟩
      | effect op =>
        refine ⟨?_, ?_, ?_⟩
        · intro _ member _ bad
          exact bad.1 member.1
        · intro _ _ left right
          exact left.2.trans right.2.symm
        · by_cases h : ((m.effect op input).run store).Dom
          · exact .inl h
          · exact .inr ⟨_, h, rfl⟩
    | gamma =>
      obtain ⟨input, store⟩ := input
      cases input with
      | cons tag payload => exact child tag.down (payload, store)
  | theta => exact theta_consistent m (body (0 : Fin 1)) (bad (0 : Fin 1)) (child (0 : Fin 1)) input

private theorem consistent (m : Model.{u,v,w} P E σ) (t : Term (Instruction P E) args past sigs outs)
    (path : Path) (input : Tuple (Values m.value) args) (locals : Locals (Values m.value) past)
    (store : σ) : Classified (runOpen m t input locals store) (abnormalAt m path t input locals store) := by
  induction t generalizing path store with
  | ret => exact ⟨fun _ _ _ h => h, fun _ _ h _ => h.elim, .inl (_root_.Part.some_dom _)⟩
  | bind node children rest ihChild ihRest =>
    unfold runOpen
    rw [Term.denoteOpenWith, StateT.run_bind]
    exact (kind_consistent m node.kind path _
      (fun j input => (children j).denoteOpenWith (interpretation m) input PUnit.unit)
      (fun j x => abnormalAt m (path ++ [(_, j.val)]) (children j) x.1 PUnit.unit x.2)
      (fun j x => ihChild j _ x.1 PUnit.unit x.2) (node.inputs.read input locals, store)).bind
      (fun x => ihRest path input (locals.snoc x.1) x.2)

theorem return_excludes_abnormal (m : Model.{u,v,w} P E σ)
    (g : Graph (Instruction P E) args [] sigs outs) (input : Tuple (Values m.value) args) (store : σ)
    {output : Configuration m.value σ outs} (returned : output ∈ observe m g input store)
    (obs : Abnormal E m.value σ) : ¬ abnormal m g input store obs :=
  (consistent m g.toTerm [] input PUnit.unit store).disjoint output returned obs

theorem abnormal_unique (m : Model.{u,v,w} P E σ)
    (g : Graph (Instruction P E) args [] sigs outs) (input : Tuple (Values m.value) args) (store : σ)
    {a b : Abnormal E m.value σ} (left : abnormal m g input store a) (right : abnormal m g input store b) :
    a = b :=
  (consistent m g.toTerm [] input PUnit.unit store).unique a b left right

theorem endpoint_exists (m : Model.{u,v,w} P E σ)
    (g : Graph (Instruction P E) args [] sigs outs) (input : Tuple (Values m.value) args) (store : σ) :
    (observe m g input store).Dom ∨ ∃ obs, abnormal m g input store obs :=
  (consistent m g.toTerm [] input PUnit.unit store).exists_endpoint

end Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Partial.Proofs

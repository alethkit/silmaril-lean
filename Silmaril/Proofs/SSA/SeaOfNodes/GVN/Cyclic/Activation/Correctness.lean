module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation
open Diamond (Model Signature Ty Val ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Origin Port Tuple Wires)
open Loop (appendTuple)

universe u v w

private theorem same_port {T : Type u} {ts : List T} {t : T}
    (a b : Port ts t) (same : a.index = b.index) : a = b := by
  induction a with
  | head => cases b <;> simp_all [Port.index]
  | tail _ ih =>
    cases b with
    | head => simp [Port.index] at same
    | tail b => exact congrArg Port.tail (ih b (Nat.succ.inj same))

private theorem get_headerLatch {T : Type u} {F : T → Type w} {xs ys : List T} {t : T}
    (fixed : Tuple F xs) (carried : Tuple F ys) (port : Port ys t) :
    (appendTuple carried fixed).get (headerLatch port xs) = carried.get port := by
  induction fixed with
  | nil => rfl
  | cons _ _ ih => exact ih

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out t : ValueSort Data} {n : Nat} {sorts : Fin n → ValueSort Data}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable {g : Cyclic.Graph Op inputs sorts} {p : Partition n} {m : Model.{u,v,w} Op}

private theorem get_headerInput {F : Ty Data → Type w} {tail : List (Ty Data)}
    (port : Port inputs t) (fixed : Tuple F (dataPorts inputs)) (rest : Tuple F tail) :
    (appendTuple rest fixed).get (headerInput tail port) = fixed.get (inputSlot port) := by
  induction port with
  | head => cases fixed; rfl
  | tail _ ih => cases fixed with | cons _ fixed => exact ih fixed

private theorem read_input (input : Inputs m inputs) (old : Inputs m carried) (port : Port inputs t) :
    headerRead loop m input old (.arg (headerInput (dataPorts carried) port)) =
      input.get (inputSlot port) :=
  get_headerInput port input old

private theorem read_latch (input : Inputs m inputs) (old : Inputs m carried)
    (port : Port (dataPorts carried) (.value t)) :
    headerRead loop m input old (.arg (headerLatch port (dataPorts inputs))) = old.get port :=
  get_headerLatch input old port

private theorem read_cast {a b : ValueSort Data} (h : a = b) (wire : HeaderWire inputs carried headerSigs a)
    (input : Inputs m inputs) (old : Inputs m carried) :
    HEq (headerRead loop m input old (h ▸ wire)) (headerRead loop m input old wire) := by
  cases h
  rfl

section Compare

variable {sites : ∀ i, Site loop sorts (sorts i)}
variable {input₁ input₂ : Inputs m inputs} {old₁ old₂ : Inputs m carried}

private theorem source_agree (fixed : InputsAgree m input₁ input₂)
    (a b : Source inputs sorts t) (same : a.address.relabel p = b.address.relabel p)
    (previous : ∀ i j, a.address = .producer t i → b.address = .producer t j →
      p i = p j → (sites i).value m input₁ old₁ = (sites j).value m input₂ old₂) :
    headerRead loop m input₁ old₁ (sourceWire sites a) =
      headerRead loop m input₂ old₂ (sourceWire sites b) := by
  cases a with
  | argument a =>
    cases b with
    | argument b =>
      have indexEq : a.index = b.index := (Address.argument.inj same).2
      have portEq := same_port a b indexEq
      subst b
      exact (read_input input₁ old₁ a).trans ((fixed a).trans (read_input input₂ old₂ a).symm)
    | producer => cases same
  | producer i type₁ =>
    cases b with
    | argument => cases same
    | producer j type₂ =>
      have ij : p i = p j := (Address.producer.inj same).2
      have packed := previous i j rfl rfl ij
      have values := (Sigma.mk.inj packed).2
      exact eq_of_heq ((read_cast type₁ (sites i).origin input₁ old₁).trans
        (values.trans (read_cast type₂ (sites j).origin input₂ old₂).symm))

private theorem operand_values {ins : List (ValueSort Data)} (fixed : InputsAgree m input₁ input₂)
    (xs ys : Tuple (Source inputs sorts) ins)
    (same : (Source.addresses xs).map (Address.relabel p) = (Source.addresses ys).map (Address.relabel p))
    (previous : ∀ {t} i j, .producer t i ∈ (Source.addresses xs) → .producer t j ∈ (Source.addresses ys) →
      p i = p j → (sites i).value m input₁ old₁ = (sites j).value m input₂ old₂) :
    (operandWires sites xs).read (appendTuple old₁ input₁)
      (loop.header.eval m (appendTuple old₁ input₁) PUnit.unit) =
    (operandWires sites ys).read (appendTuple old₂ input₂)
      (loop.header.eval m (appendTuple old₂ input₂) PUnit.unit) := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys =>
      have both : _ :: _ = _ :: _ := same
      obtain ⟨head, tail⟩ := List.cons.inj both
      have headVal := source_agree (sites := sites) (old₁ := old₁) (old₂ := old₂) fixed x y head
        (fun i j left right eq =>
          previous i j (List.mem_cons.mpr (.inl left.symm)) (List.mem_cons.mpr (.inl right.symm)) eq)
      have tailVal := ih ys tail (fun i j left right eq =>
        previous i j (List.mem_cons_of_mem _ left) (List.mem_cons_of_mem _ right) eq)
      simp only [operandWires, Wires.read, Tuple.map] at tailVal ⊢
      exact congrArg₂ Tuple.cons headVal tailVal

private theorem read_primitive {ins : List (ValueSort Data)} (opcode : Op ins t)
    (operands : Tuple (Source inputs sorts) ins) (producer : Producer loop.header t)
    (valid : (Site.pure opcode operands producer).Valid sites)
    (input : Inputs m inputs) (old : Inputs m carried) :
    headerRead loop m input old producer.origin =
      m.run opcode ((operandWires sites operands).read (appendTuple old input)
        (loop.header.eval m (appendTuple old input) PUnit.unit)) := by
  have eval := producer.read_key m (appendTuple old input) PUnit.unit
  change producer.key = ⟨_, opcode, operandWires sites operands⟩ at valid
  rw [valid] at eval
  exact eval

private theorem site_values {a b : ValueSort Data}
    (s₁ : Site loop sorts a) (s₂ : Site loop sorts b)
    (valid₁ : s₁.Valid sites) (valid₂ : s₂.Valid sites)
    (fixed : InputsAgree m input₁ input₂)
    (latches : s₁.latchValue m old₁ = s₂.latchValue m old₂)
    (profile : s₁.node.profile = s₂.node.profile)
    (operands : s₁.node.addresses.map (Address.relabel p) = s₂.node.addresses.map (Address.relabel p))
    (earlier : ∀ {t} i j, s₁.node.isPure = true → s₂.node.isPure = true →
      .producer t i ∈ s₁.node.addresses → .producer t j ∈ s₂.node.addresses →
      p i = p j → (sites i).value m input₁ old₁ = (sites j).value m input₂ old₂) :
    s₁.value m input₁ old₁ = s₂.value m input₂ old₂ := by
  cases s₁ with
  | phi _ _ port₁ =>
    cases s₂ with
    | phi _ _ port₂ =>
      simp only [Site.value, Site.origin, read_latch]
      exact Option.some.inj latches
    | pure => cases profile
  | pure op₁ wires₁ ref₁ =>
    cases s₂ with
    | phi => cases profile
    | pure op₂ wires₂ ref₂ =>
      rename_i ins₁ ins₂
      have opProfile := Sum.inr.inj profile
      have sameIns : ins₁ = ins₂ := congrArg Sigma.fst opProfile
      subst ins₂
      have rest := eq_of_heq (Sigma.mk.inj opProfile).2
      have sameOut : a = b := congrArg Sigma.fst rest
      subst b
      have sameOpcode := eq_of_heq (Sigma.mk.inj rest).2
      subst op₂
      have values := operand_values (sites := sites) (old₁ := old₁) (old₂ := old₂) fixed wires₁ wires₂
        operands (fun i j left right eq => earlier i j rfl rfl left right eq)
      simp only [Site.value, Site.origin, read_primitive _ _ _ valid₁, read_primitive _ _ _ valid₂, values]

end Compare

private theorem site_keys (view : View g loop) (stable : Stable g p) {i j : Fin n}
    (same : p i = p j) :
    (view.site i).node.profile = (view.site j).node.profile ∧
      (view.site i).node.addresses.map (Address.relabel p) =
        (view.site j).node.addresses.map (Address.relabel p) := by
  simpa only [view.shape, Graph.operandClasses] using stable i j same

theorem classes_agree (view : View g loop) (stable : Stable g p)
    {input₁ input₂ : Inputs m inputs} {old₁ old₂ : Inputs m carried}
    (fixed : InputsAgree m input₁ input₂) (latches : view.LatchesAgree p m old₁ old₂) :
    view.ClassesAgree p m input₁ old₁ input₂ old₂ := by
  intro i j
  induction rankEq : i.val + j.val using Nat.strongRecOn generalizing i j with
  | ind rank ih =>
    intro same
    obtain ⟨profile, operands⟩ := site_keys view stable same
    apply site_values (view.site i) (view.site j) (view.valid i) (view.valid j)
      fixed (latches i j same) profile operands
    intro t a b pureA pureB memA memB eq
    have smallerA := g.ordered i a t (by simpa only [view.shape] using pureA)
      (by simpa only [view.shape] using memA)
    have smallerB := g.ordered j b t (by simpa only [view.shape] using pureB)
      (by simpa only [view.shape] using memB)
    exact ih (a.val + b.val) (by omega) a b rfl eq

theorem read_source_agrees (view : View g loop)
    {input₁ input₂ : Inputs m inputs} {old₁ old₂ : Inputs m carried}
    (fixed : InputsAgree m input₁ input₂) (classes : view.ClassesAgree p m input₁ old₁ input₂ old₂)
    (a b : Source inputs sorts t) (same : a.address.relabel p = b.address.relabel p) :
    headerRead loop m input₁ old₁ (sourceWire view.site a) =
      headerRead loop m input₂ old₂ (sourceWire view.site b) :=
  source_agree fixed a b same (fun i j _ _ eq => classes i j eq)

private theorem read_initial_latch {a : ValueSort Data}
    (input : Inputs m inputs) (entry : Port inputs a) (port : Port (dataPorts carried) (.value a))
    (valid : (loop.phiInputs .entry).get port = .arg (inputSlot entry)) :
    (loop.initial m input).get port = input.get (inputSlot entry) := by
  have read := loop.latch_get m .entry input (loop.preheader.eval m input PUnit.unit) port
  rw [valid] at read
  exact read

private theorem initial_sites {a b : ValueSort Data} {sites : ∀ i, Site loop sorts (sorts i)}
    (s₁ : Site loop sorts a) (s₂ : Site loop sorts b)
    (valid₁ : s₁.Valid sites) (valid₂ : s₂.Valid sites)
    {input₁ input₂ : Inputs m inputs} (fixed : InputsAgree m input₁ input₂)
    (profile : s₁.node.profile = s₂.node.profile)
    (operands : s₁.node.addresses.map (Address.relabel p) = s₂.node.addresses.map (Address.relabel p)) :
    s₁.latchValue m (loop.initial m input₁) = s₂.latchValue m (loop.initial m input₂) := by
  cases s₁ with
  | pure => cases s₂ <;> first | rfl | cases profile
  | phi entry₁ _ port₁ =>
    cases s₂ with
    | pure => cases profile
    | phi entry₂ _ port₂ =>
      have sameSort : a = b := Sum.inl.inj profile
      subst b
      have entryEq := same_port entry₁ entry₂ (Address.argument.inj (List.cons.inj operands).1).2
      subst entry₂
      simp only [Site.latchValue, read_initial_latch input₁ entry₁ port₁ valid₁.1,
        read_initial_latch input₂ entry₁ port₂ valid₂.1, fixed entry₁]

theorem initial_agree (view : View g loop) (stable : Stable g p)
    {input₁ input₂ : Inputs m inputs} (fixed : InputsAgree m input₁ input₂) :
    view.LatchesAgree p m (loop.initial m input₁) (loop.initial m input₂) := by
  intro i j same
  obtain ⟨profile, operands⟩ := site_keys view stable same
  exact initial_sites (view.site i) (view.site j) (view.valid i) (view.valid j) fixed profile operands

private def feedback (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (m : Model.{u,v,w} Op) (input : Inputs m inputs) (old : Inputs m carried) : Inputs m carried :=
  let args := appendTuple old input
  loop.latch m .backedge args (loop.header.eval m args PUnit.unit)

private theorem read_feedback {a : ValueSort Data}
    (input : Inputs m inputs) (old : Inputs m carried) (port : Port (dataPorts carried) (.value a))
    (wire : HeaderWire inputs carried headerSigs a) (valid : (loop.phiInputs .backedge).get port = wire) :
    (feedback loop m input old).get port = headerRead loop m input old wire := by
  have read := loop.latch_get m .backedge (appendTuple old input)
    (loop.header.eval m (appendTuple old input) PUnit.unit) port
  rw [valid] at read
  exact read

private theorem feedback_sites {a b : ValueSort Data} (view : View g loop)
    (s₁ : Site loop sorts a) (s₂ : Site loop sorts b)
    (valid₁ : s₁.Valid view.site) (valid₂ : s₂.Valid view.site)
    {input₁ input₂ : Inputs m inputs} {old₁ old₂ : Inputs m carried}
    (fixed : InputsAgree m input₁ input₂) (classes : view.ClassesAgree p m input₁ old₁ input₂ old₂)
    (profile : s₁.node.profile = s₂.node.profile)
    (operands : s₁.node.addresses.map (Address.relabel p) = s₂.node.addresses.map (Address.relabel p)) :
    s₁.latchValue m (feedback loop m input₁ old₁) = s₂.latchValue m (feedback loop m input₂ old₂) := by
  cases s₁ with
  | pure => cases s₂ <;> first | rfl | cases profile
  | phi _ back₁ port₁ =>
    cases s₂ with
    | pure => cases profile
    | phi _ back₂ port₂ =>
      have sameSort : a = b := Sum.inl.inj profile
      subst b
      have key := (List.cons.inj (List.cons.inj operands).2).1
      have valueEq := read_source_agrees view fixed classes back₁ back₂ key
      simp only [Site.latchValue, read_feedback input₁ old₁ port₁ _ valid₁.2,
        read_feedback input₂ old₂ port₂ _ valid₂.2, valueEq]

theorem step_agrees (view : View g loop) (stable : Stable g p)
    {input₁ input₂ : Inputs m inputs} {old₁ old₂ : Inputs m carried}
    (fixed : InputsAgree m input₁ input₂) (latches : view.LatchesAgree p m old₁ old₂) :
    headerRead loop m input₁ old₁ loop.predicate = headerRead loop m input₂ old₂ loop.predicate ∧
      view.OutcomesAgree p m (loop.step m input₁ old₁) (loop.step m input₂ old₂) := by
  have classes := classes_agree view stable fixed latches
  have guard : headerRead loop m input₁ old₁ loop.predicate =
      headerRead loop m input₂ old₂ loop.predicate := by
    rw [view.guard_eq]
    exact read_source_agrees view fixed classes view.guard view.guard rfl
  have result : headerRead loop m input₁ old₁ loop.result =
      headerRead loop m input₂ old₂ loop.result := by
    rw [view.result_eq]
    exact read_source_agrees view fixed classes view.result view.result rfl
  refine ⟨guard, ?_⟩
  change view.OutcomesAgree p m
    (if (headerRead loop m input₁ old₁ loop.predicate).down then .inr (feedback loop m input₁ old₁)
     else .inl (headerRead loop m input₁ old₁ loop.result))
    (if (headerRead loop m input₂ old₂ loop.predicate).down then .inr (feedback loop m input₂ old₂)
     else .inl (headerRead loop m input₂ old₂ loop.result))
  rw [guard]
  split
  · intro i j same
    obtain ⟨profile, operands⟩ := site_keys view stable same
    exact feedback_sites view (view.site i) (view.site j) (view.valid i) (view.valid j)
      fixed classes profile operands
  · exact result

private theorem replace_exit_step (view : View g loop) (stable : Stable g p)
    (input : Inputs m inputs) (old : Inputs m carried) (latches : view.LatchesAgree p m old old)
    (replacement : Source inputs sorts out)
    (same : view.result.address.relabel p = replacement.address.relabel p) :
    ({ loop with result := sourceWire view.site replacement } :
      Loop.Graph Op inputs carried entrySigs headerSigs out).step m input old = loop.step m input old := by
  have fixed : InputsAgree m input input := fun _ => rfl
  have classes := classes_agree view stable fixed latches
  have result := read_source_agrees view fixed classes view.result replacement same
  rw [← view.result_eq] at result
  change (if (headerRead loop m input old loop.predicate).down then .inr (feedback loop m input old)
    else .inl (headerRead loop m input old (sourceWire view.site replacement))) = loop.step m input old
  rw [← result]
  rfl

private theorem replace_exit_eval (view : View g loop) (stable : Stable g p)
    (input : Inputs m inputs) (old : Inputs m carried) (latches : view.LatchesAgree p m old old)
    (replacement : Source inputs sorts out)
    (same : view.result.address.relabel p = replacement.address.relabel p) (budget : Nat) :
    ({ loop with result := sourceWire view.site replacement } :
      Loop.Graph Op inputs carried entrySigs headerSigs out).evalFrom m input budget old =
      loop.evalFrom m input budget old := by
  induction budget generalizing old with
  | zero =>
    simp only [Loop.Graph.evalFrom, replace_exit_step view stable input old latches replacement same]
  | succ budget ih =>
    simp only [Loop.Graph.evalFrom, replace_exit_step view stable input old latches replacement same]
    cases taken : loop.step m input old with
    | inl _ => rfl
    | inr next =>
      have fixed : InputsAgree m input input := fun _ => rfl
      have outcome := (step_agrees view stable fixed latches).2
      rw [taken] at outcome
      exact ih next outcome

theorem redirect_eval (view : View g loop) [DecidableEq (ValueSort Data)]
    [∀ ins out, DecidableEq (Op ins out)] (p : Partition n) (replacement : Source inputs sorts out)
    (m : Model.{u,v,w} Op) (input : Inputs m inputs) (budget : Nat) :
    (view.redirectResult p replacement).evalBackedges m budget input = loop.evalBackedges m budget input := by
  unfold View.redirectResult
  split
  · have accepted := Bool.and_eq_true_iff.mp ‹_›
    have stable := (checkStable_eq_true_iff g p).mp accepted.1
    have same := of_decide_eq_true accepted.2
    exact replace_exit_eval view stable input (loop.initial m input)
      (initial_agree view stable (fun _ => rfl)) replacement same budget
  · rfl

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation

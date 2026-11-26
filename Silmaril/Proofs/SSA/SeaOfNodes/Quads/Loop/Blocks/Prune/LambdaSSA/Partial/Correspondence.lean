module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Denotation
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial.Proofs

open Diamond (Model ValueSort sortValue)
open Diamond.LambdaSSA (Atom Primitive inputEnv instruction instruction_deterministic)
open Isotope (Value)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Region (Eval)
open SeaOfNodes.Loop.LambdaSSA

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data} {σ : Type x}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable (m : Model.{u, v, w} Op) (input : Bank (regs := regs) m)
variable {p : Program Op regs out} {code : Region (Primitive Op)}
variable (start : σ)

theorem mem_observe_iff_eval (result : Observation m σ) :
    result ∈ observe m input code start ↔
      Eval (instruction m) (inputEnv m input) code start result.1 result.2.1 result.2.2 := by
  have witness (h : (observe m input code start).Dom) :
      let chosen := (observe m input code start).get h
      Eval (instruction m) (inputEnv m input) code start chosen.1 chosen.2.1 chosen.2.2 :=
    Classical.choose_spec h
  constructor
  · rintro ⟨h, rfl⟩
    exact witness h
  · intro evaluated
    let h : (observe m input code start).Dom := ⟨result, evaluated⟩
    obtain ⟨label, payload, state⟩ := Eval.deterministic (instruction_deterministic m) (witness h) evaluated
    exact ⟨h, Prod.ext label (Prod.ext payload state)⟩

private theorem source_mem_iff (p : Program Op regs out) (result : sortValue m.value out) :
    result ∈ p.lower.denote m input ↔ ∃ budget, p.evalBackedges m budget input = some result :=
  (p.lower.returns_iff_mem_denote m input result).symm.trans
    ((p.lower.returns_iff_evalBackedges m input result).trans
      (exists_congr fun budget => by rw [p.lower_evalBackedges m input budget]))

variable (emitted : lower p = some code)
include emitted

theorem observe_eq :
    observe m input code start =
      (p.lower.denote m input).map (fun result => (0, Generic.packResult m (out := out) result, start)) := by
  apply Part.ext
  rintro ⟨label, payload, finish⟩
  rw [mem_observe_iff_eval, lower_eval_iff emitted m input start finish label payload, Part.mem_map_iff]
  constructor
  · rintro ⟨result, returned, rfl, rfl, rfl⟩
    exact ⟨result, (source_mem_iff m input p result).2 returned, rfl⟩
  · rintro ⟨result, returned, equal⟩
    obtain ⟨tag, rest⟩ := Prod.mk.inj equal
    obtain ⟨samePayload, sameState⟩ := Prod.mk.inj rest
    exact ⟨result, (source_mem_iff m input p result).1 returned, tag.symm, samePayload.symm, sameState.symm⟩

theorem observe_eq_none_iff :
    observe m input code start = Part.none ↔ ∀ budget, p.evalBackedges m budget input = none := by
  rw [observe_eq m input start emitted, Part.eq_none_iff]
  constructor
  · intro absent budget
    cases source : p.evalBackedges m budget input with
    | none => rfl
    | some result =>
      exact (absent _ (Part.mem_map _ ((source_mem_iff m input p result).2 ⟨budget, source⟩))).elim
  · intro absent _ observed
    obtain ⟨result, native, _⟩ := (Part.mem_map_iff _).1 observed
    obtain ⟨budget, run⟩ := (source_mem_iff m input p result).1 native
    rw [absent budget] at run
    cases run

theorem mem_observe_iff_run [DecidableEq Data] (label : Nat) (payload : Value (Atom m)) (finish : σ) :
    (label, payload, finish) ∈ observe m input code start ↔
      (∃ fuel, Generic.Fuel.run m (inputEnv m input) fuel code = some (label, payload)) ∧ finish = start := by
  rw [mem_observe_iff_eval, lower_eval_iff emitted m input start finish label payload]
  constructor
  · rintro ⟨result, ⟨budget, returned⟩, rfl, rfl, rfl⟩
    exact ⟨⟨budget + 1, by rw [run_succ emitted, returned]; rfl⟩, rfl⟩
  · rintro ⟨⟨fuel, run⟩, rfl⟩
    cases fuel with
    | zero =>
      rw [run_zero emitted] at run
      cases run
    | succ budget =>
      rw [run_succ emitted, Option.map_eq_some_iff] at run
      obtain ⟨result, returned, equal⟩ := run
      obtain ⟨tag, samePayload⟩ := Prod.mk.inj equal
      exact ⟨result, ⟨budget, returned⟩, tag.symm, samePayload.symm, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial.Proofs

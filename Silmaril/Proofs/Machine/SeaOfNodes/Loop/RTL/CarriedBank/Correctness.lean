module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Defs

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Proofs

open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA (Inputs word)
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Diamond (Val sortValue)

theorem initial_bank (args : Inputs Word) :
    graph.initial model (input args) = bank args.first args.second 0 := rfl

theorem feedback_bank (args : Inputs Word) (first second index : Word) :
    let ports := appendTuple (bank first second index) (input args)
    graph.latch model .backedge ports (graph.header.eval model ports PUnit.unit) =
      bank second first (index + 1) := rfl

theorem incoming_operand (edge : Incoming) :
    ((lowerFunc.block? (incomingSlot edge).1).bind
      fun block => block.term.args[(incomingSlot edge).2]?) =
      some (1, incomingRegisters edge) := by
  cases edge <;> rfl

theorem step_entry (fr : Frame Reg) (stack : List (Activation Reg)) (mem : Memory) (first second : Word)
    (hf : fr.get (.arg 1) = some first) (hs : fr.get (.arg 2) = some second)
    (hi : fr.get (.pre 0) = some 0) :
    step lower ⟨⟨0, 0, preheader.ops.length⟩, fr, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr first second 0, stack, mem⟩ := by
  change transfer lower _ 1 [.arg 1, .arg 2, .pre 0] = _
  simp [transfer, Frame.readAll, hf, hs, hi]
  rfl

theorem step_feedback (fr : Frame Reg) (stack : List (Activation Reg)) (mem : Memory)
    (first second next guard : Word)
    (hf : fr.get .first = some first) (hs : fr.get .second = some second)
    (hi : fr.get (.node 1) = some next) (hc : fr.get (.node 0) = some guard) (taken : guard ≠ 0) :
    step lower ⟨⟨0, 1, header.ops.length⟩, fr, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr second first next, stack, mem⟩ := by
  change (match fr.get (.node 0) with
    | none => Result.stuck (R := Reg)
    | some guard => transfer lower _ (if guard = 0 then 2 else 1)
        (if guard = 0 then [.node 2] else [.second, .first, .node 1])) = _
  rw [hc]
  simp only [ite_eq_right taken]
  simp [transfer, Frame.readAll, hf, hs, hi]
  rfl

private theorem source_step (args : Inputs Word) (first second index : Word) :
    graph.step model (input args) (bank first second index) =
      if index.toNat < args.limit.toNat then .inr (bank second first (index + 1))
      else .inl (first - second) := by
  change (if decide (index.toNat < args.limit.toNat) then
      Sum.inr (α := Word) (bank second first (index + 1)) else Sum.inl (first - second)) = _
  by_cases test : index.toNat < args.limit.toNat <;> (simp [test]; rfl)

private theorem source_total_from (args : Inputs Word) (first second index : Word) :
    ∃ value : Word, graph.ReturnsAfter model (input args) (args.limit.toNat - index.toNat)
      (bank first second index) value := by
  generalize hcount : args.limit.toNat - index.toNat = count
  induction count generalizing first second index with
  | zero =>
    have stop : ¬ index.toNat < args.limit.toNat := by omega
    exact ⟨first - second, .exit ((source_step args first second index).trans (ite_eq_right stop))⟩
  | succ count ih =>
    have keep : index.toNat < args.limit.toNat := by omega
    have increment : (index + 1).toNat = index.toNat + 1 := by
      rw [BitVec.toNat_add]
      change (index.toNat + 1) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt (by have := args.limit.isLt; omega)
    obtain ⟨value, rest⟩ := ih second first (index + 1) (by omega)
    exact ⟨value, .backedge ((source_step args first second index).trans (ite_eq_left keep)) rest⟩

theorem source_returns_at_limit (args : Inputs Word) :
    ∃ value : Word, graph.ReturnsAfter model (input args) args.limit.toNat
      (graph.initial model (input args)) value :=
  source_total_from args args.first args.second 0

private abbrev Carried := Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Carried model

private structure FrameMatches (fr : Frame Reg) (args : Inputs Word) (first second index : Word) : Prop where
  limit : fr.get (.arg 0) = some args.limit
  one : fr.get .one = some 1
  first : fr.get .first = some first
  second : fr.get .second = some second
  index : fr.get .index = some index

private def guardWord (args : Inputs Word) (index : Word) : Word :=
  ofBool (decide (index.toNat < args.limit.toNat))

private def afterHeader (fr : Frame Reg) (args : Inputs Word) (first second index : Word) : Frame Reg :=
  ((fr.set (.node 0) (guardWord args index)).set (.node 1) (index + 1)).set (.node 2) (first - second)

private def atPoint (label pc : Nat) (fr : Frame Reg) (mem : Memory) : State Reg :=
  ⟨⟨0, label, pc⟩, fr, [], mem⟩

/-- Prepend the three actual producer instructions to a counted suffix. -/
private theorem header_prefix {args : Inputs Word} {first second index : Word} {fr : Frame Reg}
    (matched : FrameMatches fr args first second index) (mem : Memory) {n : Nat} {finish : State Reg}
    (tail : StepsNWithin lower [] n (atPoint 1 3 (afterHeader fr args first second index) mem) finish) :
    StepsNWithin lower [] (n + 3) (atPoint 1 0 fr mem) finish := by
  let compared := fr.set (.node 0) (guardWord args index)
  let advanced := compared.set (.node 1) (index + 1)
  have compare :
      (Op.binary (.cmp .ltu) (.node 0) .index (.arg 0)).exec fr mem = some (compared, mem) := by
    simp only [Op.exec, matched.index, matched.limit, Option.bind_some]
    rfl
  have advance :
      (Op.binary .add (.node 1) .index .one).exec compared mem = some (advanced, mem) := by
    have readIndex : compared.get .index = some index := by simpa [compared] using matched.index
    have readOne : compared.get .one = some 1 := by simpa [compared] using matched.one
    simp only [Op.exec, readIndex, readOne, Option.bind_some]
    rfl
  have observe :
      (Op.binary .sub (.node 2) .first .second).exec advanced mem =
        some (afterHeader fr args first second index, mem) := by
    have readFirst : advanced.get .first = some first := by simpa [advanced, compared] using matched.first
    have readSecond : advanced.get .second = some second := by simpa [advanced, compared] using matched.second
    simp only [Op.exec, readFirst, readSecond, Option.bind_some]
    rfl
  have s₀ := Transition.op (p := lower) (s := atPoint 1 0 fr mem) rfl compare
  have s₁ := Transition.op (p := lower) (s := atPoint 1 1 compared mem) rfl advance
  have s₂ := Transition.op (p := lower) (s := atPoint 1 2 advanced mem) rfl observe
  exact .head ⟨s₀.step_eq, List.nil_suffix⟩
    (.head ⟨s₁.step_eq, List.nil_suffix⟩ (.head ⟨s₂.step_eq, List.nil_suffix⟩ tail))

private theorem exit_step (fr : Frame Reg) (mem : Memory) (result : Word)
    (read : fr.get (.node 2) = some result) (stop : fr.get (.node 0) = some 0) :
    step lower (atPoint 1 3 fr mem) = .running (atPoint 2 0 (fr.set .result result) mem) := by
  change (match fr.get (.node 0) with
    | none => Result.stuck (R := Reg)
    | some guard => transfer lower _ (if guard = 0 then 2 else 1)
        (if guard = 0 then [.node 2] else [.second, .first, .node 1])) = _
  rw [stop]
  simp [transfer, Frame.readAll, read, atPoint]
  rfl

private theorem counted_header (args : Inputs Word) (mem : Memory) {n : Nat}
    {latched : Carried} {value : sortValue model.value word}
    (source : graph.ReturnsAfter model (input args) n latched value) :
    ∀ (first second index : Word) (fr : Frame Reg),
      latched = bank first second index → FrameMatches fr args first second index →
      ∃ finish, StepsNWithin lower [] (4 * (n + 1)) (atPoint 1 0 fr mem) finish ∧
        step lower finish = .returned [value] mem := by
  refine Graph.ReturnsAfter.rec (g := graph) (m := model) (input := input args)
    (motive := fun count old result _ =>
      ∀ (first second index : Word) (fr : Frame Reg),
        old = bank first second index → FrameMatches fr args first second index →
        ∃ finish, StepsNWithin lower [] (4 * (count + 1)) (atPoint 1 0 fr mem) finish ∧
          step lower finish = .returned [result] mem) ?_ ?_ source
  · intro old result taken first second index fr same matched
    subst old
    have route := (source_step args first second index).symm.trans taken
    have stop : ¬ index.toNat < args.limit.toNat := by
      intro keep
      rw [ite_eq_left keep] at route
      cases route
    have valueEq := Sum.inl.inj ((ite_eq_right stop).symm.trans route)
    let after := afterHeader fr args first second index
    have test : after.get (.node 0) = some 0 := by
      change some (guardWord args index) = some 0
      simp [guardWord, ofBool, stop]
    refine ⟨atPoint 2 0 (after.set .result (first - second)) mem,
      header_prefix matched mem (.head ⟨exit_step after mem _ rfl test, List.nil_suffix⟩ .refl), ?_⟩
    rw [← valueEq]
    rfl
  · intro count old next result taken _ ih first second index fr same matched
    subst old
    have route := (source_step args first second index).symm.trans taken
    have keep : index.toNat < args.limit.toNat := by
      by_contra stop
      rw [ite_eq_right stop] at route
      cases route
    have nextEq := Sum.inr.inj (route.symm.trans (ite_eq_left keep))
    let after := afterHeader fr args first second index
    have hf : after.get .first = some first := by simpa [after, afterHeader] using matched.first
    have hs : after.get .second = some second := by simpa [after, afterHeader] using matched.second
    have test : after.get (.node 0) = some 1 := by
      change some (guardWord args index) = some 1
      simp [guardWord, ofBool, keep]
    have feedback := step_feedback after [] mem first second (index + 1) 1 hf hs rfl test (by decide)
    let nextFrame := bindBank after second first (index + 1)
    have nextMatches : FrameMatches nextFrame args second first (index + 1) :=
      ⟨by simpa [nextFrame, bindBank, after, afterHeader] using matched.limit,
       by simpa [nextFrame, bindBank, after, afterHeader] using matched.one, rfl, rfl, rfl⟩
    obtain ⟨finish, rest, observed⟩ := ih second first (index + 1) nextFrame nextEq nextMatches
    exact ⟨finish, header_prefix matched mem (.head ⟨feedback, List.nil_suffix⟩ rest), observed⟩

private def entryFrame (args : Inputs Word) : Frame Reg :=
  ((Frame.empty.set (.arg 0) args.limit).set (.arg 1) args.first).set (.arg 2) args.second

private theorem counted_entry (args : Inputs Word) (mem : Memory) {n : Nat} {value : Word}
    (source : graph.ReturnsAfter model (input args) n (graph.initial model (input args)) value) :
    ∃ start finish, lower.start 0 (wordArgs args) mem = some start ∧
      StepsNWithin lower [] (4 * n + 7) start finish ∧ step lower finish = .returned [value] mem := by
  let fr := entryFrame args
  let seeded := fr.set (.pre 0) 0
  let prepared := seeded.set .one 1
  let next := bindBank prepared args.first args.second 0
  have seed := Transition.op (p := lower) (s := atPoint 0 0 fr mem)
    (o := .const (.pre 0) 0) rfl (rfl : _ = some (seeded, mem))
  have one := Transition.op (p := lower) (s := atPoint 0 1 seeded mem)
    (o := .const .one 1) rfl (rfl : _ = some (prepared, mem))
  have enter := step_entry prepared [] mem args.first args.second rfl rfl rfl
  obtain ⟨finish, rest, observed⟩ := counted_header args mem source args.first args.second 0 next
    (initial_bank args) ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨atPoint 0 0 fr mem, finish, rfl,
    .head ⟨seed.step_eq, List.nil_suffix⟩ (.head ⟨one.step_eq, List.nil_suffix⟩
      (.head ⟨enter, List.nil_suffix⟩ rest)), observed⟩

private theorem source_to_oracle (args : Inputs Word) (mem : Memory) {value : Word}
    (source : graph.Returns model (input args) value) :
    lower.oracle 0 (wordArgs args) mem [value] mem := by
  obtain ⟨_, run⟩ := source
  obtain ⟨start, finish, started, steps, observed⟩ := counted_entry args mem run
  exact ⟨start, started, finish, stepsWithin_nil_iff.mp steps.toStepsWithin, observed⟩

theorem lower_returns_iff (args : Inputs Word) (initial final : Memory) (returned : List Word) :
    lower.oracle 0 (wordArgs args) initial returned final ↔
      ∃ value : Word, graph.Returns model (input args) value ∧ returned = [value] ∧ final = initial := by
  constructor
  · intro actual
    obtain ⟨value, run⟩ := source_returns_at_limit args
    have source : graph.Returns model (input args) value := ⟨_, run⟩
    have expected := source_to_oracle args initial source
    obtain ⟨valuesEq, memEq⟩ :=
      Prog.oracle_deterministic lower 0 (wordArgs args) initial _ _ _ _ actual expected
    exact ⟨value, source, valuesEq, memEq⟩
  · rintro ⟨value, source, rfl, memEq⟩
    subst final
    exact source_to_oracle args initial source

private theorem return_length_unique {n j : Nat} {s a b : State Reg}
    {values other : List Word} {mem final : Memory}
    (left : StepsNWithin lower [] n s a) (leftRet : step lower a = .returned values mem)
    (right : StepsNWithin lower [] j s b) (rightRet : step lower b = .returned other final) :
    n = j := by
  induction left generalizing j b with
  | refl =>
    cases right with
    | refl => rfl
    | head next _ => cases leftRet.symm.trans next.1
  | head next _ ih =>
    cases right with
    | refl => cases rightRet.symm.trans next.1
    | head other rest =>
      cases Step.deterministic next.1 other.1
      exact congrArg Nat.succ (ih leftRet rest rightRet)

theorem lower_stepsN_iff (args : Inputs Word) (initial final : Memory) (returned : List Word)
    (running : Nat) :
    (∃ start finish, lower.start 0 (wordArgs args) initial = some start ∧
      StepsNWithin lower [] running start finish ∧ step lower finish = .returned returned final) ↔
    ∃ (backedges : Nat) (value : Word), graph.ReturnsAfter model (input args) backedges
      (graph.initial model (input args)) value ∧ running = 4 * backedges + 7 ∧
        returned = [value] ∧ final = initial := by
  constructor
  · rintro ⟨start, finish, started, steps, observed⟩
    have actual : lower.oracle 0 (wordArgs args) initial returned final :=
      ⟨start, started, finish, stepsWithin_nil_iff.mp steps.toStepsWithin, observed⟩
    obtain ⟨value, run⟩ := source_returns_at_limit args
    obtain ⟨start', finish', started', steps', observed'⟩ := counted_entry args initial run
    obtain rfl := Option.some.inj (started'.symm.trans started)
    have expected : lower.oracle 0 (wordArgs args) initial [value] initial :=
      source_to_oracle args initial ⟨_, run⟩
    obtain ⟨valuesEq, memEq⟩ :=
      Prog.oracle_deterministic lower 0 (wordArgs args) initial _ _ _ _ actual expected
    exact ⟨args.limit.toNat, value, run, return_length_unique steps observed steps' observed', valuesEq, memEq⟩
  · rintro ⟨backedges, value, run, rfl, rfl, memEq⟩
    subst final
    exact counted_entry args initial run

end Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Proofs

module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Defs

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Proofs

open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (CallOracle Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg entry model word)
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Diamond (Val sortValue)
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming appendTuple)

private abbrev Carried := Tuple (Val model.value) [.value word]

private abbrev carry (old : Word) : Carried := .cons old .nil

private theorem carry_eta (latched : Carried) : ∃ old : Word, carry old = latched := by
  cases latched with
  | cons old rest =>
    cases rest
    exact ⟨old, rfl⟩

private theorem source_step (seed delta old : Word) :
    graph.step model (entry seed delta) (.cons old .nil) =
      if old - delta = 0 then .inl old else .inr (.cons (old - delta) .nil) := by
  change (if (old - delta != (0 : Word)) = true then Sum.inr (α := Word) (carry (old - delta))
    else Sum.inl old) = _
  by_cases h : old - delta = 0 <;> (simp [h]; rfl)

theorem incoming_operand (edge : Incoming) :
    ((lowerFunc.block? (incomingSlot edge).1).bind
      fun block => block.term.args[(incomingSlot edge).2]?) =
      some (1, [incomingRegister edge]) := by
  cases edge <;> rfl

theorem latch_entry (seed delta : Word) :
    graph.initial model (entry seed delta) = .cons seed .nil := rfl

theorem latch_feedback (seed delta old : Word) :
    let args := appendTuple (Tuple.cons (F := Val model.value) (t := .value word) old .nil) (entry seed delta)
    graph.latch model .backedge args (graph.header.eval model args PUnit.unit) =
      .cons (old - delta) .nil := rfl

theorem transfer_incoming (edge : Incoming) (s : State Reg) (value : Word)
    (func : s.point.func = 0) (read : s.frame.get (incomingRegister edge) = some value) :
    transfer lower s 1 [incomingRegister edge] =
      .running ⟨⟨0, 1, 0⟩, s.frame.set .phi value, s.stack, s.mem⟩ := by
  simp [transfer, Frame.readAll, read, func]
  rfl

private theorem predicate_zero (next : Word) : nonzeroWord next = 0 ↔ next = 0 := by
  by_cases h : next = 0 <;> simp [nonzeroWord, h, ofBool]

private theorem get_old (fr : Frame Reg) (old delta : Word)
    (hold : fr.get .phi = some old) :
    (headerFrame fr old delta).get .phi = some old := by
  simpa [headerFrame] using hold

private theorem get_delta (fr : Frame Reg) (old delta : Word)
    (hdelta : fr.get (.arg 1) = some delta) :
    (headerFrame fr old delta).get (.arg 1) = some delta := by
  simpa [headerFrame] using hdelta

/-- Successful non-call execution determines the first intermediate state. -/
private theorem ops_cons_iff {oracle : CallOracle} {op : Op Reg} {ops : List (Op Reg)}
    {fr next done : Frame Reg} {m n final : Memory}
    (exec : op.exec fr m = some (next, n)) :
    Ops.Exec oracle (op :: ops) fr m done final ↔ Ops.Exec oracle ops next n done final := by
  constructor
  · intro run
    cases run with
    | op step rest =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (step.symm.trans exec))
      exact rest
    | call => simp [Op.exec] at exec
  · exact Ops.Exec.op exec

theorem header_exec_iff (oracle : CallOracle) (fr done : Frame Reg) (m final : Memory)
    (old delta : Word) (hold : fr.get .phi = some old)
    (hdelta : fr.get (.arg 1) = some delta) :
    Ops.Exec oracle header.ops fr m done final ↔
      done = headerFrame fr old delta ∧ final = m := by
  let sub := fr.set (.node 0) (old - delta)
  let zero := sub.set (.node 1) 0
  have subtract : (Op.binary .sub (.node 0) .phi (.arg 1)).exec fr m = some (sub, m) := by
    simp only [Op.exec, hold, hdelta, Option.bind_some]
    rfl
  have compare :
      (Op.binary (.cmp .ne) (.node 2) (.node 0) (.node 1)).exec zero m =
        some (headerFrame fr old delta, m) := rfl
  change Ops.Exec oracle
    [Op.binary .sub (.node 0) .phi (.arg 1), .const (.node 1) 0,
      .binary (.cmp .ne) (.node 2) (.node 0) (.node 1)] fr m done final ↔ _
  rw [ops_cons_iff subtract,
    ops_cons_iff (show (Op.const (.node 1) 0).exec sub m = some (zero, m) from rfl),
    ops_cons_iff compare]
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .nil

theorem step_entry (fr : Frame Reg) (stack : List (Activation Reg))
    (mem : Memory) (seed : Word) (read : fr.get (.arg 0) = some seed) :
    step lower ⟨⟨0, 0, 0⟩, fr, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, fr.set .phi seed, stack, mem⟩ := by
  change transfer lower _ 1 [incomingRegister .entry] = _
  exact transfer_incoming .entry _ seed rfl read

theorem step_feedback (fr : Frame Reg) (stack : List (Activation Reg))
    (mem : Memory) (old delta : Word) (taken : old - delta ≠ 0) :
    let after := headerFrame fr old delta
    step lower ⟨⟨0, 1, header.ops.length⟩, after, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, after.set .phi (old - delta), stack, mem⟩ := by
  change transfer lower _ (if nonzeroWord (old - delta) = 0 then 2 else 1)
    (if nonzeroWord (old - delta) = 0 then [.phi] else [incomingRegister .backedge]) = _
  rw [ite_eq_right (mt (predicate_zero _).mp taken), ite_eq_right (mt (predicate_zero _).mp taken)]
  exact transfer_incoming .backedge _ _ rfl rfl

private theorem header_complete (oracle : CallOracle) (seed delta : Word)
    (result : sortValue model.value word)
    (mem : Memory) {count : Nat} {latch : Carried}
    (run : graph.ReturnsAfter model (entry seed delta) count latch result) :
    ∀ (fr : Frame Reg), fr.get .phi = some (latch.get .head) → fr.get (.arg 1) = some delta →
      Func.Exec oracle lowerFunc 1 fr mem (.returned [result] mem) := by
  refine Graph.ReturnsAfter.rec (g := graph) (m := model) (input := entry seed delta) (motive := fun _ latch result _ =>
    ∀ (fr : Frame Reg), fr.get .phi = some (latch.get .head) → fr.get (.arg 1) = some delta →
      Func.Exec oracle lowerFunc 1 fr mem (.returned [result] mem)) ?_ ?_ run
  · intro latch result taken fr hold hdelta
    obtain ⟨old, rfl⟩ := carry_eta latch
    have taken := (source_step seed delta old).symm.trans taken
    have hzero : old - delta = 0 := by
      by_contra h
      rw [ite_eq_right h] at taken
      cases taken
    have heq := Sum.inl.inj ((ite_eq_left hzero).symm.trans taken)
    have hcond := (predicate_zero _).mpr hzero
    let after := headerFrame fr old delta
    refine .cond (b := header) (bt := exitBlock) (x := nonzeroWord (old - delta))
      (vals := [old]) (fr₂ := after.set (.node 3) old) rfl
      ((header_exec_iff oracle fr after mem mem old delta hold hdelta).mpr ⟨rfl, rfl⟩)
      rfl rfl ?_ ?_ rfl ?_
    · change after.readAll (if nonzeroWord (old - delta) = 0 then [.phi] else [.node 0]) = _
      rw [ite_eq_left hcond]
      have read : after.get .phi = some old := get_old fr old delta hold
      simp [Frame.readAll, read]
    · exact (congrArg lowerFunc.block? (ite_eq_left hcond)).trans rfl
    · simp only [ite_eq_left hcond]
      rw [← heq]
      refine .ret (b := exitBlock) rfl .nil rfl ?_
      simp [Frame.readAll]
  · intro _ latch next result taken _ ih fr hold hdelta
    obtain ⟨old, rfl⟩ := carry_eta latch
    have taken := (source_step seed delta old).symm.trans taken
    have hne : old - delta ≠ 0 := by
      intro h
      rw [ite_eq_left h] at taken
      cases taken
    obtain rfl := Sum.inr.inj ((ite_eq_right hne).symm.trans taken)
    have hcond := mt (predicate_zero _).mp hne
    let after := headerFrame fr old delta
    refine .cond (b := header) (bt := header) (x := nonzeroWord (old - delta))
      (vals := [old - delta]) (fr₂ := after.set .phi (old - delta)) rfl
      ((header_exec_iff oracle fr after mem mem old delta hold hdelta).mpr ⟨rfl, rfl⟩)
      rfl rfl ?_ ?_ rfl ?_
    · change after.readAll (if nonzeroWord (old - delta) = 0 then [.phi] else [.node 0]) = _
      exact (congrArg after.readAll (ite_eq_right hcond)).trans rfl
    · exact (congrArg lowerFunc.block? (ite_eq_right hcond)).trans rfl
    · simp only [ite_eq_right hcond]
      exact ih _ rfl (get_delta fr old delta hdelta)

private theorem exit_sound {oracle : CallOracle} {fr : Frame Reg} {mem : Memory}
    {out : Exit} {old : Word} (hold : fr.get (.node 3) = some old)
    (run : Func.Exec oracle lowerFunc 2 fr mem out) :
    out = .returned [old] mem := by
  cases run with
  | ret hb hops hterm hargs =>
    obtain rfl := Option.some.inj (show some exitBlock = _ from hb)
    change Ops.Exec _ [] _ _ _ _ at hops
    cases hops
    cases hterm
    have values := Option.some.inj ((by simp [Frame.readAll, hold] :
      fr.readAll [.node 3] = some [old]).symm.trans hargs)
    rw [← values]
  | jump hb _ hterm _ _ _ _ | cond hb _ hterm _ _ _ _ _ | trap hb _ hterm =>
    obtain rfl := Option.some.inj (show some exitBlock = _ from hb)
    cases hterm

private theorem header_sound {oracle : CallOracle} {l : Nat} {fr : Frame Reg} {mem : Memory}
    {out : Exit} (run : Func.Exec oracle lowerFunc l fr mem out) (seed delta : Word) :
    l = 1 → ∀ old : Word, fr.get .phi = some old → fr.get (.arg 1) = some delta →
      ∃ count result, graph.ReturnsAfter model (entry seed delta) count (.cons old .nil) result ∧
        out = .returned [result] mem := by
  induction run with
  | @cond _ _ _ _ _ _ _ _ _ _ before _ _ _ _ _ hb hops hterm hc hargs ht hw rest ih =>
    rintro rfl old hold hdelta
    obtain rfl := Option.some.inj (show some header = _ from hb)
    obtain ⟨rfl, rfl⟩ := (header_exec_iff oracle _ _ _ _ old delta hold hdelta).mp hops
    change Term.cond (R := Reg) (.node 2) 1 [.node 0] 2 [.phi] = _ at hterm
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Term.cond.inj hterm
    have predicate := Option.some.inj ((rfl : (headerFrame before old delta).get (.node 2) =
      some (nonzeroWord (old - delta))).symm.trans hc)
    subst_vars
    by_cases hzero : old - delta = 0
    · have hbranch := (predicate_zero _).mpr hzero
      simp only [ite_eq_left hbranch] at hargs ht rest
      obtain rfl := Option.some.inj (show some exitBlock = _ from ht)
      have read : (headerFrame before old delta).readAll [.phi] = some [old] := by
        simp [Frame.readAll, get_old before old delta hold]
      obtain rfl := Option.some.inj (read.symm.trans hargs)
      obtain rfl := Option.some.inj (show some ((headerFrame before old delta).set (.node 3) old) = _ from hw)
      exact ⟨0, old, .exit ((source_step seed delta old).trans (ite_eq_left hzero)), exit_sound rfl rest⟩
    · have hbranch := mt (predicate_zero _).mp hzero
      simp only [ite_eq_right hbranch] at hargs ht rest ih
      obtain rfl := Option.some.inj (show some header = _ from ht)
      obtain rfl := Option.some.inj ((rfl : (headerFrame before old delta).readAll [.node 0] =
        some [old - delta]).symm.trans hargs)
      obtain rfl := Option.some.inj (show some ((headerFrame before old delta).set .phi (old - delta)) = _ from hw)
      obtain ⟨count, result, run, returned⟩ := ih trivial (old - delta) rfl (get_delta before old delta hdelta)
      exact ⟨count + 1, result, .backedge ((source_step seed delta old).trans (ite_eq_right hzero)) run, returned⟩
  | jump hb _ hterm _ _ _ _ _ | ret hb _ hterm _ | trap hb _ hterm =>
    intro hl
    subst_vars
    obtain rfl := Option.some.inj (show some header = _ from hb)
    cases hterm

private def entryFrame (seed delta : Word) : Frame Reg :=
  (Frame.empty.set (.arg 0) seed).set (.arg 1) delta

private theorem entry_exec_iff (oracle : CallOracle) (seed delta : Word) (mem : Memory) (out : Exit) :
    Func.Exec oracle lowerFunc 0 (entryFrame seed delta) mem out ↔
      ∃ result, graph.Returns model (entry seed delta) result ∧ out = .returned [result] mem := by
  constructor
  · intro run
    cases run with
    | jump hb hops hterm hargs ht hw rest =>
      obtain rfl := Option.some.inj (show some preheader = _ from hb)
      change Ops.Exec _ [] _ _ _ _ at hops
      cases hops
      change Term.jump (R := Reg) 1 [.arg 0] = _ at hterm
      obtain ⟨rfl, rfl⟩ := Term.jump.inj hterm
      obtain rfl := Option.some.inj ((rfl : (entryFrame seed delta).readAll [.arg 0] =
        some [seed]).symm.trans hargs)
      obtain rfl := Option.some.inj (show some header = _ from ht)
      obtain rfl := Option.some.inj (show some ((entryFrame seed delta).set .phi seed) = _ from hw)
      obtain ⟨count, result, run, observed⟩ := header_sound rest seed delta rfl seed rfl rfl
      exact ⟨result, ⟨count, run⟩, observed⟩
    | cond hb _ hterm _ _ _ _ _ | ret hb _ hterm _ | trap hb _ hterm =>
      obtain rfl := Option.some.inj (show some preheader = _ from hb)
      cases hterm
  · rintro ⟨result, ⟨count, run⟩, rfl⟩
    refine .jump (b := preheader) (bt := header) (vals := [seed])
      (fr₂ := (entryFrame seed delta).set .phi seed) rfl .nil rfl rfl rfl rfl ?_
    exact header_complete oracle seed delta result mem run _ rfl rfl

theorem lower_returns_iff (seed delta : Word) (initial final : Memory) (returned : List Word) :
    lower.oracle 0 [seed, delta] initial returned final ↔
      ∃ value : Word, graph.Returns model (entry seed delta) value ∧
        returned = [value] ∧ final = initial := by
  have bridge :
      Func.Exec lower.oracle lowerFunc 0 (entryFrame seed delta) initial (.returned returned final) ↔
        lower.oracle 0 [seed, delta] initial returned final :=
    Func.exec_returned_iff_oracle (p := lower) (f := 0) (fn := lowerFunc)
      (b := preheader) rfl rfl rfl
  have returns := entry_exec_iff lower.oracle seed delta initial (.returned returned final)
  constructor
  · intro run
    obtain ⟨value, source, observed⟩ := returns.mp (bridge.mpr run)
    obtain ⟨valuesEq, memEq⟩ := Exit.returned.inj observed
    exact ⟨value, source, valuesEq, memEq⟩
  · rintro ⟨value, source, rfl, rfl⟩
    exact bridge.mp (returns.mpr ⟨value, source, rfl⟩)

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Proofs

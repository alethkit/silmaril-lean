import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (FuncAddr Frame Value)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall
open Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph (Program)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private def expected : V1.FuncType := ⟨[.int .i64, .int .i32], [.int .i64]⟩
private def reversed : V1.FuncType := ⟨expected.params.reverse, expected.results⟩

private def target (signature : V1.FuncType) (body : List Ranked.Graph.Op) : Ranked.Graph.Function :=
  ⟨⟨{ types := [signature] }, ⟨0⟩, signature.params, [], signature.results⟩, 0, [], body⟩

private def returningFn : Ranked.Graph.Function := target expected [.numeric (.get ⟨0⟩)]
private def mismatchFn : Ranked.Graph.Function := target reversed [.numeric (.get ⟨1⟩)]
private def trappingFn : Ranked.Graph.Function := target expected [.unreachable]
private def functions : List Ranked.Graph.Function := [returningFn, mismatchFn, trappingFn]
private def program : Program := ⟨functions.map some⟩
private def site : Site := ⟨⟨[some ⟨0⟩, none, some ⟨1⟩, some ⟨2⟩], some 4⟩, ⟨1⟩, expected⟩

-- The site has no directly resolvable aliases for its indirect callees.
private def caller : Frame := ⟨[i32 91], { tables := [⟨1⟩], types := [reversed, expected] }⟩
private def saved : List Value := [i32 7]
private def operands : List Value := [i64 42, i32 5]
private def coreRest : List Core.Admin := [.plain .nop]
private def limeRest : List Lime1.Execution.Admin := [.source .nop]

private def coreStore : Core.Store Unit :=
  { funcs := functions.map Ranked.Graph.Function.coreInstance
    tables := [(⟨[], none⟩ : Execution.Runtime.TableInst).toCore, site.table.toCore] }

private def limeStore : Lime1.Execution.Store Unit :=
  { funcs := functions.map fun fn => .wasm fn.declaration.type fn.declaration.module fn.limeFunc
    tables := [⟨[], none⟩, site.table] }

private theorem coreAllocated : program.CoreAllocated coreStore := by
  intro addr fn found
  cases slot : functions[addr.value]? <;> simp_all [Program.lookup, program, coreStore, List.getElem?_map]

private theorem limeAllocated : program.LimeAllocated limeStore := by
  intro addr fn found
  cases slot : functions[addr.value]? <;> simp_all [Program.lookup, program, limeStore, List.getElem?_map]

private theorem checked : site.check program caller = true := rfl
example : program.checkDirect = true := rfl
example : site.resolve program 0 = some (.resolved ⟨0⟩) := rfl
example : site.resolve program 1 = some .null := rfl
example : site.resolve program 2 = some (.mismatch ⟨1⟩) := rfl
example : site.resolve program 3 = some (.resolved ⟨2⟩) := rfl
example : site.resolve program 4 = some .bounds := rfl
example : site.resolve program (-1) = some .bounds := rfl

-- Nonexistent type indices and dangling entries are outside the site guard.
private def invalidType : Site := { site with typeIndex := ⟨2⟩ }
example : invalidType.check program caller = false := rfl
example : invalidType.resolve program 1 = some .null := rfl
example : invalidType.resolve program (-1) = some .bounds := rfl
example : site.check (⟨[]⟩ : Program) caller = false := rfl
example : site.resolve (⟨[]⟩ : Program) 0 = none := rfl

-- Bounds takes precedence even when the type index would fail the site guard.
example : Lime1.Execution.Step CallFrame.limeNoHost
    (limeSource limeStore caller invalidType (-1) (saved ++ operands) limeRest)
    (limeResolved limeStore caller (saved ++ operands) limeRest .bounds) :=
  .context (.callIndirectBounds limeStore caller invalidType.typeIndex (-1) site.table rfl rfl)
    (saved ++ operands) limeRest

private theorem coreExact {out : Outcome} {selector : BitVec 32} (resolved : site.resolve program selector = some out) :
    out.coreTrace.IsChain (fun a b => ∀ dst,
      Core.Step Numerics.Profile.spec noHost (coreConfig coreStore caller site selector (saved ++ operands) coreRest a) dst ↔
        dst = coreConfig coreStore caller site selector (saved ++ operands) coreRest b) :=
  core_trace_exact checked coreAllocated (addr := 1) rfl resolved

private theorem limeExact {out : Outcome} {selector : BitVec 32} (resolved : site.resolve program selector = some out)
    {dst : Lime1.Execution.Config Unit} :
    Lime1.Execution.Step CallFrame.limeNoHost (limeSource limeStore caller site selector (saved ++ operands) limeRest) dst ↔
      dst = limeResolved limeStore caller (saved ++ operands) limeRest out :=
  lime_step_iff checked limeAllocated rfl resolved

example := coreExact (selector := 0) (out := .resolved ⟨0⟩) rfl
example := coreExact (selector := 1) (out := .null) rfl
example := coreExact (selector := 2) (out := .mismatch ⟨1⟩) rfl
example := coreExact (selector := -1) (out := .bounds) rfl

example (dst : Lime1.Execution.Config Unit) :
    Lime1.Execution.Step CallFrame.limeNoHost (limeSource limeStore caller site 0 (saved ++ operands) limeRest) dst ↔
      dst = ⟨limeStore, caller, Lime1.Execution.values (saved ++ operands) ++ [.invoke ⟨0⟩, .source .nop]⟩ :=
  limeExact (selector := 0) (out := .resolved ⟨0⟩) rfl

example (dst : Lime1.Execution.Config Unit) :
    Lime1.Execution.Step CallFrame.limeNoHost (limeSource limeStore caller site 1 (saved ++ operands) limeRest) dst ↔
      dst = ⟨limeStore, caller, Lime1.Execution.values (saved ++ operands) ++ [.trap, .source .nop]⟩ :=
  limeExact (selector := 1) (out := .null) rfl

example (dst : Lime1.Execution.Config Unit) :
    Lime1.Execution.Step CallFrame.limeNoHost (limeSource limeStore caller site 2 (saved ++ operands) limeRest) dst ↔
      dst = ⟨limeStore, caller, Lime1.Execution.values (saved ++ operands) ++ [.trap, .source .nop]⟩ :=
  limeExact (selector := 2) (out := .mismatch ⟨1⟩) rfl

example (dst : Lime1.Execution.Config Unit) :
    Lime1.Execution.Step CallFrame.limeNoHost (limeSource limeStore caller site (-1) (saved ++ operands) limeRest) dst ↔
      dst = ⟨limeStore, caller, Lime1.Execution.values (saved ++ operands) ++ [.trap, .source .nop]⟩ :=
  limeExact (selector := -1) (out := .bounds) rfl

example (dst : Core.Config Unit) :
    Core.Step Numerics.Profile.spec noHost (coreConfig coreStore caller site 0 (saved ++ operands) coreRest (.call (some ⟨0⟩))) dst ↔
      dst = coreEntered coreStore caller returningFn saved operands coreRest :=
  core_enter_iff (site := site) (selector := 0) coreAllocated rfl rfl rfl

example (dst : Lime1.Execution.Config Unit) :
    Lime1.Execution.Step CallFrame.limeNoHost (limeResolved limeStore caller (saved ++ operands) limeRest (.resolved ⟨0⟩)) dst ↔
      dst = limeEntered limeStore caller returningFn saved operands limeRest :=
  lime_enter_iff (site := site) (selector := 0) limeAllocated rfl rfl rfl

example : program.FrameEdge ⟨0⟩ (.invoke operands)
    (.label (returningFn.declaration.frame operands).locals (.running returningFn.initial returningFn.code)) :=
  resolved_frame_entry (site := site) (selector := 0) rfl rfl rfl

-- A matching signature can still enter a body which traps. The saved operand
-- and pending nop survive resolution and entry, then the trap bypasses the nop.
private theorem coreCalleeTrap :
    Core.Steps Numerics.Profile.spec noHost (coreConfig coreStore caller site 3 (saved ++ operands) coreRest .start)
      ⟨coreStore, caller.toCore, [.trap]⟩ := by
  have resolvedPath := core_trace_reachable (coreExact (selector := 3) (out := .resolved ⟨2⟩) rfl)
    (phase := .call (some ⟨2⟩)) (by decide)
  have enter : Core.Step Numerics.Profile.spec noHost
      (coreConfig coreStore caller site 3 (saved ++ operands) coreRest (.call (some ⟨2⟩)))
      (coreEntered coreStore caller trappingFn saved operands coreRest) :=
    (core_enter_iff (site := site) (selector := 3) coreAllocated rfl rfl rfl).mpr rfl
  let inner := (trappingFn.declaration.frame operands).toCore
  let c : List Core.Val := saved.map Value.toCore
  have lift {before after : List Core.Admin}
      (move : Core.Step Numerics.Profile.spec noHost ⟨coreStore, caller.toCore, before⟩ ⟨coreStore, caller.toCore, after⟩) :
      Core.Step Numerics.Profile.spec noHost ⟨coreStore, caller.toCore, Core.vals c ++ before ++ coreRest⟩
        ⟨coreStore, caller.toCore, Core.vals c ++ after ++ coreRest⟩ := by
    simpa only [List.append_assoc] using Core.Sim.Step.vals_left (Core.Sim.Step.append_right move coreRest) c
  have raise : Core.Step Numerics.Profile.spec noHost
      ⟨coreStore, caller.toCore, [.frame 1 inner [.label 1 [] [.plain .unreachable]]]⟩
      ⟨coreStore, caller.toCore, [.frame 1 inner [.label 1 [] [.trap]]]⟩ :=
    .ctxtFrame (.ctxtLabel (.parametric .unreachable))
  have leaveLabel : Core.Step Numerics.Profile.spec noHost
      ⟨coreStore, caller.toCore, [.frame 1 inner [.label 1 [] [.trap]]]⟩
      ⟨coreStore, caller.toCore, [.frame 1 inner [.trap]]⟩ := .ctxtFrame .trapLabel
  have leaveFrame : Core.Step Numerics.Profile.spec noHost
      ⟨coreStore, caller.toCore, [.frame 1 inner [.trap]]⟩ ⟨coreStore, caller.toCore, [.trap]⟩ := .trapFrame
  exact ((((resolvedPath.tail enter).tail (lift raise)).tail (lift leaveLabel)).tail (lift leaveFrame)).tail
    (.trapInstrs (.inr (by simp [coreRest])))

private theorem limeCalleeTrap :
    Lime1.Execution.Steps CallFrame.limeNoHost (limeSource limeStore caller site 3 (saved ++ operands) limeRest)
      ⟨limeStore, caller, [.trap]⟩ := by
  have resolvedPath : Lime1.Execution.Step CallFrame.limeNoHost (limeSource limeStore caller site 3 (saved ++ operands) limeRest)
      (limeResolved limeStore caller (saved ++ operands) limeRest (.resolved ⟨2⟩)) :=
    (limeExact (selector := 3) (out := .resolved ⟨2⟩) rfl).mpr rfl
  have enter : Lime1.Execution.Step CallFrame.limeNoHost
      (limeResolved limeStore caller (saved ++ operands) limeRest (.resolved ⟨2⟩))
      (limeEntered limeStore caller trappingFn saved operands limeRest) :=
    (lime_enter_iff (site := site) (selector := 3) limeAllocated rfl rfl rfl).mpr rfl
  let inner := trappingFn.declaration.frame operands
  have raise : Lime1.Execution.Step CallFrame.limeNoHost
      ⟨limeStore, caller, [.frame 1 inner [.label 1 [] [.source .unreachable]]]⟩
      ⟨limeStore, caller, [.frame 1 inner [.label 1 [] [.trap]]]⟩ :=
    .frame (.label (.pure limeStore inner .unreachable) 1 []) 1 caller
  have leaveLabel : Lime1.Execution.Step CallFrame.limeNoHost
      ⟨limeStore, caller, [.frame 1 inner [.label 1 [] [.trap]]]⟩
      ⟨limeStore, caller, [.frame 1 inner [.trap]]⟩ := .frame (.pure limeStore inner (.labelTrap 1 [])) 1 caller
  have leaveFrame : Lime1.Execution.Step CallFrame.limeNoHost
      ⟨limeStore, caller, [.frame 1 inner [.trap]]⟩ ⟨limeStore, caller, [.trap]⟩ := .pure limeStore caller (.frameTrap 1 inner)
  exact (((((Relation.ReflTransGen.single resolvedPath).tail enter).tail (.context raise saved limeRest)).tail
    (.context leaveLabel saved limeRest)).tail (.context leaveFrame saved limeRest)).tail
    (.pure limeStore caller (.trapValues (i32 7) [] limeRest))

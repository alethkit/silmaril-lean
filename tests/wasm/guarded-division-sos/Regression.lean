module

import Silmaril.Wasm.Institution.Operational.Division.Thms

open CategoryTheory Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Institution.Operational (encode)
open Silmaril.Wasm.Institution.Operational.Division
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private abbrev cfg (code : List Admin) : Config Unit := ⟨{}, {}, code⟩
private abbrev P : Profile := .deterministic (fun _ _ _ _ => false)

private abbrev saved : List Val := [.i64 99]
private abbrev after : List Admin := [.plain .nop]

private def inContext (code : List Admin) : Config Unit :=
  cfg (vals saved ++ code ++ after)

private theorem admittedAfter : AdmittedCode after :=
  fun _ h => (List.mem_singleton.mp h).symm ▸ Allowed.nop

private theorem fact {j : Judgment Unit} (r : RuleInstance Unit ⟨[], j⟩) :
    (presentation Unit).Derives j :=
  Derives.apply (R := (presentation Unit).rules) (r := ⟨[], j⟩) r (fun _ h => nomatch h)

private theorem inContext_step {xs ys : List Admin} (d : DerivesEdge (cfg xs) (cfg ys)) :
    DerivesEdge (inContext xs) (inContext ys) :=
  Derives.apply (R := (presentation Unit).rules)
    (r := ⟨[(cfg xs, cfg ys)], inContext xs, inContext ys⟩)
    (RuleInstance.context {} {} saved xs ys after (.inl (by simp)) admittedAfter)
    (fun _ h => (List.mem_singleton.mp h).symm ▸ d)

private abbrev normalStart := inContext [intConst .i32 (-7), intConst .i32 3, divOp .i32 .signed]
private abbrev normalMid := inContext [intConst .i32 (-2)]
private abbrev normalEnd := cfg (vals [.i64 99, .i32 (-2)])

private theorem signedValue : quotient .i32 .signed (-7) 3 = -2 := by decide

private theorem normalDivide : DerivesEdge normalStart normalMid := by
  apply inContext_step
  have d := fact (RuleInstance.divide {} {} .i32 .signed (-7) 3 (by decide) (by decide))
  simpa only [signedValue, DerivesEdge, codeEdge] using d

private theorem normalFinish : DerivesEdge normalMid normalEnd :=
  Derives.apply (R := (presentation Unit).rules)
    (r := ⟨[(cfg [.plain .nop], cfg [])], normalMid, normalEnd⟩)
    (RuleInstance.context {} {} [.i64 99, .i32 (-2)] [.plain .nop] [] []
      (.inl (by simp)) (fun _ h => nomatch h))
    (fun _ h => (List.mem_singleton.mp h).symm ▸ fact (.nop {} {}))

private abbrev zeroStart := inContext [intConst .i32 84, intConst .i32 0, divOp .i32 .unsigned]
private abbrev overflowStart := inContext [intConst .i64 (BitVec.intMin 64),
  intConst .i64 (-1), divOp .i64 .signed]
private abbrev pending := inContext [.trap]
private abbrev partialTrap := cfg (vals saved ++ [.trap])
private abbrev trapped := cfg [.trap]

private theorem zeroDivide : DerivesEdge zeroStart pending :=
  inContext_step (fact (.zero {} {} .i32 .unsigned 84))

private theorem overflowDivide : DerivesEdge overflowStart pending :=
  inContext_step (fact (.overflow {} {} .i64))

-- Core can erase the instruction suffix while retaining the value prefix.
private theorem partialCore : Step P noHost pending partialTrap :=
  .ctxtInstrs (vs := saved) (rest := [])
    (.trapInstrs (vs := []) (rest := after) (.inr (by simp))) (.inl (by simp))

private theorem partialBubble : DerivesEdge pending partialTrap :=
  (derives_edge_iff (derives_admitted zeroDivide).2).mpr partialCore

private theorem finishTrap : DerivesEdge partialTrap trapped :=
  fact (.trap {} {} saved [] (.inl (by simp)) (fun _ h => nomatch h))

example : Step P noHost overflowStart pending := derives_sound overflowDivide

example : Runs (coreTransitions P Unit).model
    (encode normalStart) [(), ()]
    (encode normalEnd) :=
  (runs_iff (derives_admitted normalDivide).1 [(), ()]).mp
    (.stepL normalDivide (.stepL normalFinish .refl))

example : Runs (coreTransitions P Unit).model
    (encode zeroStart) [(), (), ()]
    (encode trapped) :=
  (runs_iff (derives_admitted zeroDivide).1 [(), (), ()]).mp
    (.stepL zeroDivide (.stepL partialBubble (.stepL finishTrap .refl)))

example (h : Runs (coreTransitions P Unit).model
    (encode zeroStart) [(), (), ()]
    (encode trapped)) :
    Runs (transitionSystem Unit).model zeroStart [(), (), ()] trapped :=
  (runs_iff (derives_admitted zeroDivide).1 [(), (), ()]).mpr h

example :
    (WasmShape.institution.obj (Silmaril.Wasm.Institution.Operational.shape Unit)).Sat
      (Discrete.mk (coreTransitions P Unit).model)
      (encode normalStart, (),
        encode normalMid) :=
  (atom_iff (P := P) (derives_admitted normalDivide).1).mpr normalDivide

example :
    (guardedCore P Unit).model
      (encode pending, (), encode partialTrap) :=
  (guardedIso P Unit).hom.preserves (e := (pending, (), partialTrap)) partialBubble

example : (policy Unit).SafeAt overflowStart := policy_safe (derives_admitted overflowDivide).1

example : (policy Unit).observe trapped .trap ∧ ¬ (policy Unit).ub trapped :=
  ⟨⟨(derives_admitted finishTrap).2, rfl⟩, fun bad => bad (derives_admitted finishTrap).2⟩

private theorem notUnreachable {a : Admin} (supported : Allowed a) : a ≠ .plain .unreachable := by
  cases supported with
  | value v =>
    intro e
    have hv := congrArg Admin.val? e
    change v.toAdmin.val? = none at hv
    simp at hv
  | _ => intro h; cases h

-- Unsupported at this boundary, although native Core specifies its trap.
example :
    (policy Unit).ub (cfg [.plain .unreachable]) ∧
      Step P noHost (cfg [.plain .unreachable]) trapped ∧
      ¬ DerivesEdge (cfg [.plain .unreachable]) trapped :=
  let rejects : (policy Unit).ub (cfg [.plain .unreachable]) := fun h =>
    notUnreachable (h _ (by simp)) rfl
  ⟨rejects, .parametric .unreachable, fun d => rejects (derives_admitted d).1⟩

example : quotient .i64 .unsigned 84 7 = 12 := by decide

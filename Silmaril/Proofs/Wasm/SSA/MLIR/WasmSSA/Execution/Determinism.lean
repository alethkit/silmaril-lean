module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Execution.Defs
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution.Fragment
import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

public section

namespace Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA

open Silmaril.MLIR.WasmSSA
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile} {host : HostSemantics H}

private theorem intBody_not_bubble {s : Store H} {fr : Frame} {code : List Admin}
    {c : Config H} (body : IntBodyCode code) (bubble : Bubble s fr code c) : False := by
  obtain ⟨_, _, X, _, _, rfl, shape, _, _⟩ := bubble
  have inside := (intBodyCode_append.mp (intBodyCode_append.mp body).1).2
  rcases shape with rfl | ⟨_, rfl⟩ <;> simp [IntBodyCode, Admin.val?, IntBodyInstr] at inside

private theorem intBody_head {s : Store H} {fr : Frame} {vs : List Val} {a : Admin}
    {target : Config H} (body : IntBodyCode [a]) (head : Head P s fr vs a target) :
    famOf a ≠ .control := by
  rcases intBodyCode_family body head.good.val_none with h | h | h | rfl
  · simp [h]
  · simp [h]
  · simp [h]
  · exact (head.good.not_blocked (.inr (.inl rfl))).elim

private theorem det_heads_of_suffix {s : Store H} {fr : Frame} {a : Admin} {rest : List Admin}
    {vs₁ vs₂ args₁ args₂ extra : List Val} {c₁ c₂ : Config H}
    (values : vs₁ ++ args₁ = vs₂ ++ args₂) (suffix : args₁ = extra ++ args₂)
    (family : famOf a ≠ .control)
    (h₁ : Head (Profile.deterministic (fun _ _ _ _ => false)) s fr args₁ a c₁)
    (h₂ : Head (Profile.deterministic (fun _ _ _ _ => false)) s fr args₂ a c₂) :
    (⟨c₁.store, c₁.frame, vals vs₁ ++ c₁.code ++ rest⟩ : Config H) =
      ⟨c₂.store, c₂.frame, vals vs₂ ++ c₂.code ++ rest⟩ := by
  obtain ⟨rfl, rfl⟩ := Head.det_fam family h₁ h₂ suffix
  simp only [List.nil_append] at suffix
  subst args₁
  rw [List.append_cancel_right values]

theorem intBody_step_unique {source left right : Config H} (body : IntBodyCode source.code)
    (h₁ : Step P host source left) (h₂ : Step P host source right) : left = right := by
  have headStep {target : Config H} (h : Step P host source target) :
      HeadDec (Profile.deterministic (fun _ _ _ _ => false)) source.store source.frame
        source.code target := by
    have moved := (intBody_step (Q := Profile.deterministic (fun _ _ _ _ => false))
      (host' := noHost) h body).2.2
    exact (Step.decomp moved).resolve_right (intBody_not_bubble body)
  obtain ⟨vs₁, args₁, a, rest, c₁, first, code, head₁, rfl⟩ := fnv_headDec (headStep h₁)
  obtain ⟨vs₂, args₂, b, rest', c₂, second, _, head₂, rfl⟩ := fnv_headDec (headStep h₂)
  rw [first] at second
  simp only [Prod.mk.injEq, List.cons.injEq] at second
  obtain ⟨values, rfl, rfl⟩ := second
  have allowed : IntBodyCode [a] := by
    intro member hm
    simp only [List.mem_singleton] at hm
    subst member
    exact body a (by rw [code]; simp)
  have family := intBody_head allowed head₁
  rcases append_eq_append_suffix values with ⟨extra, suffix⟩ | ⟨extra, suffix⟩
  · exact det_heads_of_suffix values suffix family head₁ head₂
  · exact (det_heads_of_suffix values.symm suffix family head₂ head₁).symm

theorem intBody_steps {source target : Config H} (body : IntBodyCode source.code)
    (path : Steps P host source target) : target.store = source.store ∧ IntBodyCode target.code := by
  induction path with
  | refl => exact ⟨rfl, body⟩
  | tail _ step ih =>
    obtain ⟨same, flat, _⟩ := intBody_step (Q := P) (host' := host) step ih.2
    exact ⟨same.trans ih.1, flat⟩

theorem intBody_return_stuck {s : Store H} {fr : Frame} {vs : List Val} {rest : List Admin}
    {target : Config H} (flat : IntBodyCode (vals vs ++ .plain .return_ :: rest)) :
    ¬ Step P host ⟨s, fr, vals vs ++ .plain .return_ :: rest⟩ target := by
  intro step
  have moved := (intBody_step (Q := P) (host' := noHost) step flat).2.2
  have split : fnv (vals vs ++ .plain .return_ :: rest) = (vs, .plain .return_ :: rest) := by
    simp [fnv_cons_of_none (a := .plain .return_) rfl]
  exact not_step_blocked moved split (.inr (.inl rfl))

end Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA

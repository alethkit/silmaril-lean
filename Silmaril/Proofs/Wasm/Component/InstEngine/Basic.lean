module

public import Silmaril.Wasm.Component.InstEngine.Defs
public import Silmaril.Proofs.Wasm.Component.InstSem.Run

/-!
# The engine semantics with an instantiation phase: instantiation runs

* `run_start_values`, `run_start_trap`: a start phase (`StartRunI`) is a run of the transition
  system from `starting` to `readying` or `failing`, its import calls as moves;
* `engine_inst_ready`, `engine_inst_fail`: hence instantiation rounds of `engineStrategyI`;
* `engine_noStart_ready`: an instance without a start function is ready at once;
* `engine_after_start`: after a successful instantiation the plays of `engineStrategy` from the
  store the start phase left are plays of `engineStrategyI` (lifted to export calls).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstEngine

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.InstSem
open Silmaril.Wasm.Game (liftMove)

variable {E : Engine} {I : Option (IInstance E)} {imps exps : CoreIface}

theorem run_start_values {c c' : E.Config Nat}
    {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)} (h : StartRunI E imps c cs c')
    {ys : List Flat} (hf : E.status c'.1 c'.2 = .returned (.values ys)) :
    (engineLTSI E I imps exps).Run (.starting c.1 c.2)
      ((callEvs (E := sigN imps.length) cs).map .inl) (.readying c'.1) := by
  induction h with
  | nil run => exact .tau (ITrans.sdone run hf) (.nil _)
  | call run callout hh r _ ih =>
    exact .vis (ITrans.scall run callout hh) (.vis (ITrans.sret r) (ih hf))

theorem run_start_trap {c c' : E.Config Nat}
    {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)} (h : StartRunI E imps c cs c')
    (hf : E.status c'.1 c'.2 = .returned .trap) :
    (engineLTSI E I imps exps).Run (.starting c.1 c.2)
      ((callEvs (E := sigN imps.length) cs).map .inl) .failing := by
  induction h with
  | nil run => exact .tau (ITrans.strap run hf) (.nil _)
  | call run callout hh r _ ih =>
    exact .vis (ITrans.scall run callout hh) (.vis (ITrans.sret r) (ih hf))

theorem mem_of_run_round {r : Round (sigN imps.length) ((sigN exps.length).withInst Unit)}
    {y : IState E imps.length exps.length}
    (h : (engineLTSI E I imps exps).Run .fresh r.moves y) :
    r.moves ∈ engineStrategyI E I imps exps := by
  have hl := legal_rounds [r]
  simp only [roundsMoves, List.append_nil] at hl
  exact Strategy.mem_ofLTS_of_mem_traces ⟨y, h⟩ hl

/-- **A start phase returning values: instantiation succeeds**, its import calls as moves. -/
theorem engine_inst_ready {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : E.Config Nat} (hr : StartRunI E imps (J.store, E.invoke a []) cs c') {ys : List Flat}
    (hf : E.status c'.1 c'.2 = .returned (.values ys)) :
    (instRound (F := sigN exps.length) cs .ready).moves ∈ engineStrategyI E I imps exps := by
  refine mem_of_run_round (y := .ready (.idle c'.1)) ?_
  refine .vis (ITrans.start hI ha) ?_
  exact (run_start_values (exps := exps) hr hf).append (.vis ITrans.ready (.nil _))

/-- **A start phase trapping: instantiation fails**, its import calls as moves. -/
theorem engine_inst_fail {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : E.Config Nat} (hr : StartRunI E imps (J.store, E.invoke a []) cs c')
    (hf : E.status c'.1 c'.2 = .returned .trap) :
    (instRound (F := sigN exps.length) cs (.fail ())).moves ∈ engineStrategyI E I imps exps := by
  refine mem_of_run_round (y := .dead) ?_
  refine .vis (ITrans.start hI ha) ?_
  exact (run_start_trap (exps := exps) hr hf).append (.vis ITrans.fail (.nil _))

/-- **An instance without a start function is ready at once.** -/
theorem engine_noStart_ready {J : IInstance E} (hI : I = some J) (ha : J.start = none) :
    (instRound (F := sigN exps.length) (X := sigN imps.length) [] .ready).moves ∈
      engineStrategyI E I imps exps :=
  mem_of_run_round (y := .ready (.idle J.store))
    (.vis (ITrans.noStart hI ha) (.vis ITrans.ready (.nil _)))

/-! ## After instantiation -/

theorem run_lift {s : E.Store Nat} :
    ∀ {x : EState E imps.length exps.length} {p : List (Move (sigN imps.length) (sigN exps.length))}
      {y : EState E imps.length exps.length},
    (engineLTS E ⟨s, addrsOf I⟩ imps exps).Run x p y →
      (engineLTSI E I imps exps).Run (.ready x) (p.map liftMove) (.ready y)
  | _, _, _, .nil _ => .nil _
  | _, _, _, .tau h _ => by obtain ⟨m, hm, -⟩ := h; cases hm
  | _, _, _, .vis h hr => by
    obtain ⟨m, hm, ht⟩ := h
    cases hm
    exact .vis (ITrans.lift ht) (run_lift hr)

theorem path_lift {R : Type} {X F : Sig.{0}} :
    ∀ {x z : Pos X F} {p : List (Move X F)}, Path x p z →
      Path (liftPos (R := R) x) (p.map liftMove) (liftPos z)
  | _, _, _, .nil _ => .nil _
  | _, _, _, .cons hs hp => by
    refine .cons ?_ (path_lift hp)
    cases hs with
    | ask q => exact Step.ask (E := X) (F := F.withInst R) (some q)
    | call q m => exact Step.call (E := X) (F := F.withInst R) (some q) m
    | reply q m n => exact Step.reply (E := X) (F := F.withInst R) (some q) m n
    | ret q r => exact Step.ret (E := X) (F := F.withInst R) (some q) r

theorem isO_liftMove {X F : Sig.{0}} {R : Type} {o : Move X F} (h : o.IsO) :
    (liftMove (R := R) o).IsO := by
  rcases o with (_ | _) | (_ | _) <;> exact h

/-- **After a successful instantiation, the exports are served as `engineStrategy` serves them
from the store the start phase left.** -/
theorem engine_after_start {J : IInstance E} {a : E.FuncAddr} (hI : I = some J)
    (ha : J.start = some a) {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {c' : E.Config Nat} (hr : StartRunI E imps (J.store, E.invoke a []) cs c') {ys : List Flat}
    (hf : E.status c'.1 c'.2 = .returned (.values ys))
    {p : List (Move (sigN imps.length) (sigN exps.length))}
    (hp : p ∈ engineStrategy E ⟨c'.1, J.addrs⟩ imps exps) :
    (instRound (F := sigN exps.length) cs .ready).moves ++ p.map liftMove ∈
      engineStrategyI E I imps exps := by
  have hJ : addrsOf I = J.addrs := by rw [hI]; rfl
  have hrun : ∀ {p y}, (engineLTS E ⟨c'.1, J.addrs⟩ imps exps).Run (.idle c'.1) p y →
      (engineLTSI E I imps exps).Run .fresh
        ((instRound (F := sigN exps.length) cs .ready).moves ++ p.map liftMove) (.ready y) := by
    intro p y h
    have h' : (engineLTS E ⟨c'.1, addrsOf I⟩ imps exps).Run (.idle c'.1) p y := by
      rw [hJ]; exact h
    simp only [instRound, Round.moves, List.cons_append, List.append_assoc]
    exact .vis (ITrans.start hI ha) ((run_start_values (exps := exps) hr hf).append
      (.vis ITrans.ready (run_lift h')))
  have hlegal : ∀ {p}, Legal p →
      Legal ((instRound (F := sigN exps.length) (X := sigN imps.length) (R := Unit) cs
        .ready).moves ++
        p.map liftMove) := by
    rintro p ⟨z, hz⟩
    have h := (path_round (instRound (F := sigN exps.length) (X := sigN imps.length) (R := Unit)
      cs .ready)).append (path_lift (R := Unit) hz)
    exact ⟨_, h⟩
  have hext : ∀ {p₀ : List (Move (sigN imps.length) (sigN exps.length))} {o},
      (instRound (F := sigN exps.length) cs .ready).moves ++ p₀.map liftMove ∈
        engineStrategyI E I imps exps → Legal (p₀ ++ [o]) → o.IsO →
      (instRound (F := sigN exps.length) cs .ready).moves ++ (p₀ ++ [o]).map liftMove ∈
        engineStrategyI E I imps exps := by
    intro p₀ o h0 hl ho
    obtain ⟨_, hpath⟩ := hlegal hl
    rw [List.map_append, ← List.append_assoc] at hpath ⊢
    obtain ⟨x, hx, hxo⟩ := Path.concat_iff.1 hpath
    exact (engineStrategyI E I imps exps).receptive h0 hx hxo (isO_liftMove ho)
  obtain ⟨hl, u, hu, hpu⟩ := hp
  rcases hu with rfl | ⟨⟨y, hy⟩, -⟩
  · rcases hpu with hpu | ⟨p₀, o, rfl, hp₀, ho⟩
    · obtain rfl := List.prefix_nil.1 hpu
      exact Strategy.mem_ofLTS_of_mem_traces ⟨_, hrun (.nil _)⟩ (hlegal hl)
    · obtain rfl := List.prefix_nil.1 hp₀
      exact hext (Strategy.mem_ofLTS_of_mem_traces ⟨_, hrun (.nil _)⟩ (hlegal Legal.nil)) hl ho
  · rcases hpu with ⟨v, rfl⟩ | ⟨p₀, o, rfl, ⟨v, rfl⟩, ho⟩
    · obtain ⟨y₁, hy₁, -⟩ := LTS.Run.of_append hy
      exact Strategy.mem_ofLTS_of_mem_traces ⟨_, hrun hy₁⟩ (hlegal hl)
    · obtain ⟨y₁, hy₁, -⟩ := LTS.Run.of_append hy
      exact hext (Strategy.mem_ofLTS_of_mem_traces ⟨_, hrun hy₁⟩
        (hlegal (hl.of_prefix (List.prefix_append _ _)))) hl ho

end Silmaril.Proofs.Wasm.Component.InstEngine

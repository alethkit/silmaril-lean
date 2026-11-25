module

public import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Call
public import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Compiler

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Lowering

open Silmaril.Languages.Starlark (Binding LogicalOp)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState truth)

private abbrev SourceExpr := Languages.Starlark.Functions.Lowering.Expr

private abbrev evaluate (program : Program) (available : List DeclarationId)
    (expr : SourceExpr) (target : Binding) (start : Nat) :=
  denoteBody program available ((emit expr target).run start).1

private theorem scopeTrans {s t u : State} (first : SameScope s t) (second : SameScope t u) :
    SameScope s u :=
  ⟨first.1.trans second.1, first.2.trans second.2⟩

private theorem scopeFree {s t : State} (same : SameScope s t) (free : ScratchFree t) :
    ScratchFree s := fun index => same.2.symm ▸ free index

private theorem seesRebound {i : Nat} (s : State) (bindings : Binding → Option Value) :
    StateMatch i (rebind s bindings) (rebind s bindings) :=
  reboundMatch i s bindings

private theorem reboundBack {i : Nat} {s t u s' : State} (same : StateMatch 0 s t)
    (scope : SameScope u s) (after : StateMatch i (rebind u t.bindings) s') :
    StateMatch 0 u s' :=
  StateMatch.trans (scopeTransport same scope) (StateMatch.back after (Nat.zero_le _))

private theorem reboundThrough {start : Nat} {u t v : State}
    (keep : ∀ b, ¬ Scratch start b → t.bindings b = v.bindings b) :
    StateMatch start (rebind u t.bindings) (rebind u v.bindings) :=
  ⟨rfl, rfl, rfl, keep⟩

private theorem seq_eq (program : Program) (available : List DeclarationId)
    (first rest : Body) (state : State) :
    denoteBody program available (.seq first rest) state =
      Outcome.resume (denoteBody program available first state) fun
        | .next => denoteBody program available rest
        | signal => pure signal := by
  rw [denoteBody]
  rfl

private theorem assign_eq (program : Program) (available : List DeclarationId)
    (target : Binding) (expr : Languages.Starlark.Lists.Expr) (s : State) :
    denoteBody program available (assign target expr) s = commit target (denote expr s) := by
  rw [assign, denoteBody]
  simp only [Iteration.denoteSuite, denote, bind, EStateM.bind]
  cases denote expr s <;> rfl

private theorem truth_frame (value : Value) (s : State) :
    finishState (truth value s) = s := by
  cases value with
  | list | tuple | dict =>
    rw [truth, map_state]
    exact project_state _ _ s
  | _ => rfl

private theorem keep_truth {t : State} {out : Outcome Value} {flag : Bool}
    (h : Outcome.resume out truth = .ok flag t) :
    ∃ value, out = .ok value t ∧ truth value t = .ok flag t := by
  cases out with
  | error => simp [Outcome.resume] at h
  | ok value state =>
    change truth value state = .ok flag t at h
    have hs := truth_frame value state
    rw [h] at hs
    change t = state at hs
    subst state
    exact ⟨value, rfl, h⟩

private theorem branch_eq (program : Program) (available : List DeclarationId)
    (i : Nat) (yes no : Body) (s : State) (v : Value)
    (read : denote (scratchRead i) s = .ok v s) :
    denoteBody program available (.branch (scratchRead i) yes no) s =
      Outcome.resume (truth v s) (fun b t => denoteBody program available (if b then yes else no) t) := by
  rw [denoteBody, read]
  simp only [Outcome.resume]
  cases truth v s with
  | error => rfl
  | ok flag s => cases flag <;> rfl

/-- The compiled suffix may change generated scratch bindings above its offset.
The reference state has the source effects and the incoming target bindings. -/
private def Simulates (program : Program) (available : List DeclarationId) (s : State)
    (expr : SourceExpr) (out : Outcome Value) : Prop :=
  SameScope (finishState out) s ∧
  ∀ start target (t : State), StateMatch 0 s t → ScratchFree s → ¬ Scratch start target →
    match out with
    | .ok value u => ∃ final, evaluate program available expr target start t = .ok .next final ∧
        StateMatch start ((rebind u t.bindings).write target value) final
    | .error error u => ∃ final, evaluate program available expr target start t = .error error final ∧
        StateMatch start (rebind u t.bindings) final

private theorem simAtom {program : Program} {available : List DeclarationId}
    {s : State} {atom : Languages.Starlark.Lists.Expr} {out : Outcome Value}
    (safe : AtomSafe atom) (ran : Eval s atom out) :
    Simulates program available s (.atom atom) out := by
  have eval := (eval_iff_denote _ _ _).mp ran
  refine ⟨eval ▸ atomScope safe s, ?_⟩
  intro start target t same _ _
  have transported := atomTransport safe same
  rw [eval] at transported
  cases out with
  | ok value u =>
    refine ⟨(rebind u t.bindings).write target value, ?_, ?_⟩
    · rw [evaluate, emit_atom, assign_eq, transported]
      rfl
    · exact StateMatch.write (seesRebound u t.bindings) target value
  | error error u =>
    refine ⟨rebind u t.bindings, ?_, seesRebound u t.bindings⟩
    rw [evaluate, emit_atom, assign_eq, transported]
    rfl

private theorem save_ok {program : Program} {available : List DeclarationId}
    {s u t : State} {expr : SourceExpr} {value : Value} (ih : Simulates program available s expr (.ok value u))
    (start : Nat) (same : StateMatch 0 s t) (free : ScratchFree s) :
    ∃ final,
      evaluate program available expr (temporary start) (start + 1) t = .ok .next final ∧
      StateMatch start (rebind u t.bindings) final ∧
      final.bindings (temporary start) = some value := by
  obtain ⟨final, ran, after⟩ := ih.2 (start + 1) (temporary start) t same free (temporary_protected start)
  have freeU := scopeFree ih.1 free
  refine ⟨final, ran, ?_, ?_⟩
  · exact StateMatch.trans
      (StateMatch.hideWrite (seesRebound u t.bindings) freeU (Nat.le_refl _) value)
      (StateMatch.back after (Nat.le_succ _))
  · rw [← after.bindings _ (temporary_protected start)]
    exact write_temp_read (s := rebind u t.bindings) freeU start value

private theorem save_error {program : Program} {available : List DeclarationId}
    {s u t : State} {expr : SourceExpr} {error : Error}
    (ih : Simulates program available s expr (.error error u))
    (start : Nat) (same : StateMatch 0 s t) (free : ScratchFree s) :
    ∃ final,
      evaluate program available expr (temporary start) (start + 1) t = .error error final ∧
      StateMatch start (rebind u t.bindings) final := by
  obtain ⟨final, ran, after⟩ := ih.2 (start + 1) (temporary start) t same free (temporary_protected start)
  exact ⟨final, ran, StateMatch.back after (Nat.le_succ _)⟩

private theorem continueMatch {start : Nat} {s t u : State}
    (first : StateMatch start (rebind s t.bindings) u) (v : State) :
    StateMatch start (rebind v t.bindings) (rebind v u.bindings) :=
  reboundThrough first.bindings

private inductive Saved (limit : Nat) (s : State) :
    List Languages.Starlark.Lists.Expr → List Value → Prop where
  | nil : Saved limit s [] []
  | cons {index : Nat} {reads : List Languages.Starlark.Lists.Expr} {value : Value} {values : List Value} :
      index < limit → s.bindings (temporary index) = some value → Saved limit s reads values →
      Saved limit s (scratchRead index :: reads) (value :: values)

private theorem saved_read {limit : Nat} {s : State} {reads : List Languages.Starlark.Lists.Expr}
    {values : List Value} (saved : Saved limit s reads values) (free : ScratchFree s) :
    denote (operandList reads) s = .ok values s := by
  induction saved with
  | nil => rfl
  | cons _ stored _ ih =>
    simp only [operandList, List.foldr_cons, denote, bind, EStateM.bind]
    rw [show denote (scratchRead _) s = .ok _ s from read_temp free _ stored]
    dsimp only
    unfold operandList at ih
    rw [ih]
    rfl

private def SimulatesMany (program : Program) (available : List DeclarationId) (s : State)
    (expressions : List SourceExpr) (out : Outcome (List Value)) : Prop :=
  SameScope (finishState out) s ∧
  ∀ start (t : State), StateMatch 0 s t → ScratchFree s →
    let compiled := (stages expressions).run start
    match out with
    | .ok values u => ∃ final, StateMatch start (rebind u t.bindings) final ∧
        Saved compiled.2 final (compiled.1.map Prod.snd) values ∧
        ∀ rest, denoteBody program available ((compiled.1.map Prod.fst).foldr Body.seq rest) t =
          denoteBody program available rest final
    | .error error u => ∃ final, StateMatch start (rebind u t.bindings) final ∧
        ∀ rest, denoteBody program available ((compiled.1.map Prod.fst).foldr Body.seq rest) t =
          .error error final

private theorem simManyNil (program : Program) (available : List DeclarationId) (s : State) :
    SimulatesMany program available s [] (.ok [] s) := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  intro start t same _
  exact ⟨t, same_rebound same ▸ seesRebound s t.bindings, .nil, fun _ => rfl⟩

private theorem simManyHeadError {program : Program} {available : List DeclarationId}
    {s u : State} {head : SourceExpr} {tail : List SourceExpr} {error : Error}
    (ih : Simulates program available s head (.error error u)) :
    SimulatesMany program available s (head :: tail) (.error error u) := by
  refine ⟨ih.1, ?_⟩
  intro start t same free
  obtain ⟨final, ran, after⟩ := save_error ih start same free
  rw [stages_cons]
  refine ⟨final, after, fun rest => ?_⟩
  dsimp only [evaluate] at ran
  simp only [List.map_cons, List.foldr_cons, seq_eq, ran, Outcome.resume]

private theorem simManyTail {program : Program} {available : List DeclarationId}
    {s u : State} {head : SourceExpr} {tail : List SourceExpr} {value : Value} {out : Outcome (List Value)}
    (headIH : Simulates program available s head (.ok value u))
    (tailIH : SimulatesMany program available u tail out) :
    SimulatesMany program available s (head :: tail)
      (Outcome.resume out (fun xs => pure (value :: xs))) := by
  have scope := scopeTrans tailIH.1 headIH.1
  cases out with
  | ok values last =>
    refine ⟨scope, ?_⟩
    intro start t same free
    obtain ⟨w, ran, related, stored⟩ := save_ok headIH start same free
    let next := ((emit head (temporary start)).run (start + 1)).2
    have lt : start < next := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (emit_ge _ _ _)
    obtain ⟨final, after, saved, continued⟩ :=
      tailIH.2 next w (reboundBack same headIH.1 related) (scopeFree headIH.1 free)
    rw [stages_cons]
    refine ⟨final, ?_, ?_, ?_⟩
    · exact StateMatch.trans (continueMatch related last)
        (StateMatch.back after (Nat.le_of_lt lt))
    · exact .cons (Nat.lt_of_lt_of_le lt (stages_ge tail next))
        ((after.bindings _ (fun ⟨i, h, eq⟩ => Nat.not_le_of_lt lt ((temporary_inj eq) ▸ h))).symm.trans
          (by simpa only [rebind] using stored)) saved
    · intro rest
      dsimp only [evaluate] at ran
      simp only [List.map_cons, List.foldr_cons, seq_eq, ran, Outcome.resume]
      exact continued rest
  | error error last =>
    refine ⟨scope, ?_⟩
    intro start t same free
    obtain ⟨w, ran, related, _⟩ := save_ok headIH start same free
    let next := ((emit head (temporary start)).run (start + 1)).2
    have le : start ≤ next := Nat.le_trans (Nat.le_succ _) (emit_ge _ _ _)
    obtain ⟨final, after, continued⟩ :=
      tailIH.2 next w (reboundBack same headIH.1 related) (scopeFree headIH.1 free)
    rw [stages_cons]
    refine ⟨final, StateMatch.trans (continueMatch related last) (StateMatch.back after le), ?_⟩
    intro rest
    dsimp only [evaluate] at ran
    simp only [List.map_cons, List.foldr_cons, seq_eq, ran, Outcome.resume]
    exact continued rest

private theorem simCallError {program : Program} {available : List DeclarationId}
    {s u : State} {callee : SourceExpr} {positional : List SourceExpr}
    {keywords : List (String × SourceExpr)} {star starStar : Option SourceExpr} {error : Error}
    (ih : SimulatesMany program available s (callee :: argumentExprs positional keywords star starStar)
      (.error error u)) :
    Simulates program available s (.call callee positional keywords star starStar) (.error error u) := by
  refine ⟨ih.1, ?_⟩
  intro start target t same free _
  obtain ⟨final, after, step⟩ := ih.2 start t same free
  refine ⟨final, ?_, after⟩
  rw [evaluate, emit_call]
  exact step _

private theorem simCall {program : Program} {available : List DeclarationId}
    {s u : State} {callee : SourceExpr} {positional : List SourceExpr}
    {keywords : List (String × SourceExpr)} {star starStar : Option SourceExpr}
    {values : List Value} {out : Outcome Value}
    (ih : SimulatesMany program available s (callee :: argumentExprs positional keywords star starStar)
      (.ok values u))
    (applied : Applies program available (argumentShape positional keywords star starStar) u values out) :
    Simulates program available s (.call callee positional keywords star starStar) out := by
  refine ⟨scopeTrans (applies_scope applied) ih.1, ?_⟩
  intro start target t same free _
  obtain ⟨w, related, saved, step⟩ := ih.2 start t same free
  let operands := argumentExprs positional keywords star starStar
  let shape := argumentShape positional keywords star starStar
  let collected := ((stages (callee :: operands)).run start).1
  let reads := collected.tail.map Prod.snd
  let args := fillArguments shape reads
  have relatedU := reboundBack same ih.1 related
  have freeW := StateMatch.free relatedU (scopeFree ih.1 free)
  have argLen : reads.length = shape.count := by
    have length := stages_length (callee :: operands) start
    change collected.length = operands.length + 1 at length
    simp only [reads, List.length_map, List.length_tail, length, Nat.add_sub_cancel]
    exact argument_count _ _ _ _
  obtain ⟨argsShape, argsOrdered⟩ := fill_arguments shape reads argLen
  have evaluatedArgs : denote (Arguments.operands (scratchRead start) args) w = .ok values w := by
    have ran := saved_read saved freeW
    rw [Arguments.operands, argsOrdered]
    have form : collected.map Prod.snd = scratchRead start :: reads := by
      unfold reads collected
      rw [stages_cons]
      rfl
    exact form ▸ ran
  have ran : evaluate program available (.call callee positional keywords star starStar) target start t =
      commit target (mapFrame (rebind · w.bindings) out) := by
    rw [evaluate, emit_call]
    change denoteBody program available ((collected.map Prod.fst).foldr Body.seq _) t = _
    rw [step]
    exact lower_call applied relatedU target _ _ argsShape evaluatedArgs
  cases out with
  | error error final =>
    exact ⟨_, ran, continueMatch related final⟩
  | ok value final =>
    exact ⟨_, ran, StateMatch.write (continueMatch related final) target value⟩

private theorem combine {start next : Nat} {s t w final : State}
    (first : StateMatch start (rebind s t.bindings) w) (le : start ≤ next)
    (target : Binding) (out : Outcome Value)
    (last : StateMatch next (finishState (commit target (mapFrame (rebind · w.bindings) out))) final) :
    StateMatch start (finishState (commit target (mapFrame (rebind · t.bindings) out))) final := by
  cases out with
  | error error state => exact StateMatch.trans (continueMatch first state) (StateMatch.back last le)
  | ok value state =>
    exact StateMatch.trans (StateMatch.write (continueMatch first state) target value)
      (StateMatch.back last le)

private def flowAt (out : Outcome Value) (s : State) : Outcome Flow :=
  match out with
  | .ok _ _ => .ok .next s
  | .error error _ => .error error s

private theorem withTest {program : Program} {available : List DeclarationId}
    {s u : State} {test : SourceExpr} {value : Value} {out : Outcome Value} {flag : Bool}
    (tested : Simulates program available s test (.ok value u)) (checked : truth value u = .ok flag u)
    (start : Nat) (target : Binding) (t : State) (same : StateMatch 0 s t) (free : ScratchFree s)
    (yes no : Body)
    (selected : ∀ next, StateMatch 0 u next → ScratchFree u →
      ∃ final, denoteBody program available (if flag then yes else no) next =
        flowAt out final ∧
      StateMatch start (finishState (commit target (mapFrame (rebind · next.bindings) out))) final) :
    ∃ final, denoteBody program available
        (.seq ((emit test (temporary start)).run (start + 1)).1 (.branch (scratchRead start) yes no)) t =
        flowAt out final ∧
      StateMatch start (finishState (commit target (mapFrame (rebind · t.bindings) out))) final := by
  obtain ⟨next, ran, related, stored⟩ := save_ok tested start same free
  have uFree := scopeFree tested.1 free
  have sameU : StateMatch 0 u next := reboundBack same tested.1 related
  have read := read_temp (StateMatch.free sameU uFree) start stored
  have truthEq := frameRun (frameTruth value) sameU
  rw [checked, mapFrame, same_rebound sameU] at truthEq
  obtain ⟨final, ranNext, relatedNext⟩ := selected next sameU uFree
  refine ⟨final, ?_, combine related (Nat.le_refl _) target out relatedNext⟩
  dsimp only [evaluate] at ran
  rw [seq_eq, ran, Outcome.resume]
  dsimp only
  rw [branch_eq _ _ _ _ _ _ _ read, truthEq]
  exact ranNext

private theorem failedTest {program : Program} {available : List DeclarationId}
    {s u : State} {test : SourceExpr} {tested : Outcome Value} {error : Error}
    (testIH : Simulates program available s test tested)
    (checked : Outcome.resume tested truth = .error error u)
    (start : Nat) (t : State) (same : StateMatch 0 s t) (free : ScratchFree s)
    (yes no : Body) :
    SameScope u s ∧ ∃ final,
      denoteBody program available
        (.seq ((emit test (temporary start)).run (start + 1)).1 (.branch (scratchRead start) yes no)) t =
        .error error final ∧ StateMatch start (rebind u t.bindings) final := by
  cases tested with
  | error e state =>
    have eq : e = error ∧ state = u := by simpa only [Outcome.resume, EStateM.Result.error.injEq] using checked
    obtain ⟨rfl, rfl⟩ := eq
    obtain ⟨final, ran, related⟩ := save_error testIH start same free
    refine ⟨testIH.1, final, ?_, related⟩
    dsimp only [evaluate] at ran
    rw [seq_eq, ran, Outcome.resume]
  | ok value state =>
    change truth value state = .error error u at checked
    have eq := truth_frame value state
    rw [checked] at eq
    change u = state at eq
    subst state
    obtain ⟨next, ran, related, stored⟩ := save_ok testIH start same free
    have sameU : StateMatch 0 u next := reboundBack same testIH.1 related
    have read := read_temp (StateMatch.free sameU (scopeFree testIH.1 free)) start stored
    have truthEq := frameRun (frameTruth value) sameU
    rw [checked, mapFrame, same_rebound sameU] at truthEq
    refine ⟨testIH.1, next, ?_, related⟩
    dsimp only [evaluate] at ran
    rw [seq_eq, ran, Outcome.resume]
    dsimp only
    rw [branch_eq _ _ _ _ _ _ _ read, truthEq]
    rfl

private theorem failedScope {s u : State} {tested : Outcome Value} {error : Error}
    (scope : SameScope (finishState tested) s)
    (checked : Outcome.resume tested truth = .error error u) : SameScope u s := by
  cases tested with
  | error e state =>
    have eq := congrArg finishState checked
    change state = u at eq
    exact eq ▸ scope
  | ok value state =>
    have eq := congrArg finishState checked
    change finishState (truth value state) = u at eq
    rw [truth_frame] at eq
    exact eq ▸ scope

private theorem selectAfter {program : Program} {available : List DeclarationId}
    {s t : State} {expr : SourceExpr} {out : Outcome Value}
    (ih : Simulates program available s expr out) (same : StateMatch 0 s t) (free : ScratchFree s)
    (start next : Nat) (le : start ≤ next) (target : Binding) (safe : ¬ Scratch start target) :
    ∃ final, evaluate program available expr target next t =
      flowAt out final ∧
      StateMatch start (finishState (commit target (mapFrame (rebind · t.bindings) out))) final := by
  have destSafe : ¬ Scratch next target := safe ∘ scratch_mono le
  cases out <;>
    obtain ⟨final, ran, related⟩ := ih.2 next target t same free destSafe <;>
    exact ⟨final, ran, StateMatch.back related le⟩

private theorem simBranch {program : Program} {available : List DeclarationId}
    {s u : State} {test yes no : SourceExpr} {tested out : Outcome Value} {flag : Bool}
    (a : Simulates program available s test tested) (checked : Outcome.resume tested truth = .ok flag u)
    (b : Simulates program available u (if flag then yes else no) out) :
    Simulates program available s (.branch test yes no) out := by
  obtain ⟨value, rfl, checked⟩ := keep_truth checked
  refine ⟨scopeTrans b.1 a.1, ?_⟩
  intro start target t same free safe
  let first := (emit test (temporary start)).run (start + 1)
  let left := (emit yes target).run first.2
  let right := (emit no target).run left.2
  have firstLe : start ≤ first.2 := Nat.le_trans (Nat.le_succ _) (emit_ge _ _ _)
  have secondLe : first.2 ≤ left.2 := emit_ge _ _ _
  have proved := withTest (out := out) a checked start target t same free left.1 right.1 (by
    intro w related kept
    cases flag
    · simpa only [Bool.false_eq_true, ite_false] using
        selectAfter b related kept start left.2 (Nat.le_trans firstLe secondLe) target safe
    · simpa only [ite_true] using selectAfter b related kept start first.2 firstLe target safe)
  rw [evaluate, emit_branch]
  cases out <;> exact proved

private theorem simBranchError {program : Program} {available : List DeclarationId}
    {s u : State} {test yes no : SourceExpr} {tested : Outcome Value} {error : Error}
    (ih : Simulates program available s test tested)
    (checked : Outcome.resume tested truth = .error error u) :
    Simulates program available s (.branch test yes no) (.error error u) := by
  refine ⟨failedScope ih.1 checked, ?_⟩
  intro start target t same free _
  rw [evaluate, emit_branch]
  exact (failedTest ih checked start t same free _ _).2

private theorem simLogical {program : Program} {available : List DeclarationId}
    {s u : State} {op : LogicalOp} {left right : SourceExpr} {value : Value}
    {out : Outcome Value} {flag : Bool}
    (a : Simulates program available s left (.ok value u)) (checked : truth value u = .ok flag u)
    (proceed : (if op = .and then flag else !flag) = true)
    (b : Simulates program available u right out) :
    Simulates program available s (.logical op left right) out := by
  refine ⟨scopeTrans b.1 a.1, ?_⟩
  intro start target t same free safe
  let first := (emit left (temporary start)).run (start + 1)
  let second := (emit right target).run first.2
  let keep := assign target (scratchRead start)
  have le : start ≤ first.2 := Nat.le_trans (Nat.le_succ _) (emit_ge _ _ _)
  have selected w related kept := selectAfter b (t := w) related kept start first.2 le target safe
  rw [evaluate, emit_logical]
  cases op <;> cases flag <;> simp at proceed
  · have proved := withTest (out := out) a checked start target t same free second.1 keep (by
      simpa only [ite_true] using selected)
    cases out <;> exact proved
  · have proved := withTest (out := out) a checked start target t same free keep second.1 (by
      simpa only [Bool.false_eq_true, ite_false] using selected)
    cases out <;> exact proved

private theorem simShortCircuit {program : Program} {available : List DeclarationId}
    {s u : State} {op : LogicalOp} {left right : SourceExpr} {value : Value} {flag : Bool}
    (a : Simulates program available s left (.ok value u)) (checked : truth value u = .ok flag u)
    (skip : (if op = .and then flag else !flag) = false) :
    Simulates program available s (.logical op left right) (.ok value u) := by
  refine ⟨a.1, ?_⟩
  intro start target t same free _
  obtain ⟨next, ran, related, stored⟩ := save_ok a start same free
  have sameU : StateMatch 0 u next := reboundBack same a.1 related
  have read := read_temp (StateMatch.free sameU (scopeFree a.1 free)) start stored
  have truthEq := frameRun (frameTruth value) sameU
  rw [checked, mapFrame, same_rebound sameU] at truthEq
  refine ⟨next.write target value, ?_, StateMatch.write related target value⟩
  rw [evaluate, emit_logical]
  cases op <;> cases flag <;> simp at skip
  all_goals
    dsimp only [evaluate] at ran
    rw [seq_eq, ran, Outcome.resume]
    dsimp only
    rw [branch_eq _ _ _ _ _ _ _ read, truthEq]
    change denoteBody program available (assign target (scratchRead start)) next = _
    rw [assign_eq, show denote (scratchRead start) next = .ok value next from read]
    rfl

private theorem simLogicalError {program : Program} {available : List DeclarationId}
    {s u : State} {op : LogicalOp} {left right : SourceExpr} {tested : Outcome Value} {error : Error}
    (ih : Simulates program available s left tested)
    (checked : Outcome.resume tested truth = .error error u) :
    Simulates program available s (.logical op left right) (.error error u) := by
  refine ⟨failedScope ih.1 checked, ?_⟩
  intro start target t same free _
  rw [evaluate, emit_logical]
  cases op <;> exact (failedTest ih checked start t same free _ _).2

private theorem simulates {program : Program} {available : List DeclarationId}
    {s : State} {expr : SourceExpr} {out : Outcome Value} (ran : Evaluates program available s expr out) :
    Simulates program available s expr out := by
  induction ran using Evaluates.rec
    (motive_2 := fun state expressions result _ => SimulatesMany program available state expressions result) with
  | atom safe eval => exact simAtom safe eval
  | call _ applied ih => exact simCall ih applied
  | callError _ ih => exact simCallError ih
  | branch _ checked _ test selected => exact simBranch test checked selected
  | branchError _ checked ih => exact simBranchError ih checked
  | logical _ checked proceed _ left right => exact simLogical left checked proceed right
  | shortCircuit _ checked skip left => exact simShortCircuit left checked skip
  | logicalError _ checked ih => exact simLogicalError ih checked
  | empty => exact simManyNil _ _ _
  | cons _ _ head tail => exact simManyTail head tail
  | headError _ ih => exact simManyHeadError ih
  | tailError _ _ head tail => exact simManyTail head tail

theorem preserves {program : Program} {available : List DeclarationId} {state : State}
    {expression : Languages.Starlark.Functions.Lowering.Expr} {out : Outcome Value} (ran : Evaluates program available state expression out)
    (free : ScratchFree state) (destination : Binding) (visible : ¬ Scratch 0 destination) (start : Nat) :
    match out with
    | .ok value s => ∃ targetState,
        denoteBody program available (lower expression destination start).code state = .ok .next targetState ∧
        StateMatch 0 (s.write destination value) targetState
    | .error error s => ∃ targetState,
        denoteBody program available (lower expression destination start).code state = .error error targetState ∧
        StateMatch 0 s targetState := by
  have ih := simulates ran
  have related : StateMatch 0 state state := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  have h := ih.2 start destination state related free (visible ∘ scratch_mono (Nat.zero_le _))
  cases out with
  | ok value s =>
    obtain ⟨final, ran, after⟩ := h
    have model : rebind s state.bindings = s := by
      have scope : SameScope s state := ih.1
      simp [← scope.1, rebind]
    rw [model] at after
    exact ⟨final, ran, StateMatch.back after (Nat.zero_le _)⟩
  | error error s =>
    obtain ⟨final, ran, after⟩ := h
    have scope : SameScope s state := ih.1
    have model : rebind s state.bindings = s := by simp [← scope.1, rebind]
    rw [model] at after
    exact ⟨final, ran, StateMatch.back after (Nat.zero_le _)⟩

end Silmaril.Proofs.Languages.Starlark.Functions.Lowering

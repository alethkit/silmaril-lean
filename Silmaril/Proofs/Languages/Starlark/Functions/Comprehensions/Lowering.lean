module

public import Silmaril.Languages.Starlark.Functions.Comprehensions.Defs
public import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Loop

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Comprehensions

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Comprehensions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration
open Silmaril.Proofs.Languages.Starlark.Functions.Lowering

abbrev Exact (program : Program) (available : List DeclarationId) (source lowered : Body) :=
  ∀ state, ScratchFree state →
    denoteBody program available source state = denoteBody program available lowered state ∧
    (finishState (denoteBody program available source state)).slots = state.slots

private theorem resultVisible : ¬ Scratch 0 resultSlot := by
  rintro ⟨index, _, same⟩
  have := congrArg Binding.scope same
  contradiction

private theorem operandVisible : ¬ Scratch 0 operandSlot := by
  rintro ⟨index, _, same⟩
  have := congrArg Binding.scope same
  contradiction

theorem keyVisible : ¬ Scratch 0 keySlot := by
  rintro ⟨index, _, same⟩
  have := congrArg Binding.scope same
  contradiction

theorem stage {program : Program} {available : List DeclarationId}
    {expr : Languages.Starlark.Functions.Lowering.Expr} (admitted : Admitted expr)
    (target : Binding) (start : Nat) :
    Exact program available (.assignExpr target expr) (stageLowered start target expr) := by
  intro state free
  have ran := (evaluates_iff_denoteExpr program available admitted state _).mpr rfl
  exact ⟨(scopedStage_preserves ran free target start).symm, assignExpr_slots ran target⟩

theorem seq {program : Program} {available : List DeclarationId}
    {first first' rest rest' : Body}
    (firstEq : Exact program available first first') (restEq : Exact program available rest rest') :
    Exact program available (.seq first rest) (.seq first' rest') := by
  intro state free
  obtain ⟨eqFirst, kept⟩ := firstEq state free
  rw [denoteBody.eq_def program available (.seq first rest),
    denoteBody.eq_def program available (.seq first' rest')]
  change Outcome.resume (denoteBody program available first state)
      (fun | .next => denoteBody program available rest | signal => pure signal) =
    Outcome.resume (denoteBody program available first' state)
      (fun | .next => denoteBody program available rest' | signal => pure signal) ∧ _
  simp only [← eqFirst]
  cases ran : denoteBody program available first state with
  | error => rw [ran] at kept; exact ⟨rfl, kept⟩
  | ok flow next =>
    rw [ran] at kept
    cases flow with
    | next =>
      obtain ⟨equal, after⟩ := restEq next (fun i => (congrFun kept (temporary i)).trans (free i))
      exact ⟨equal, after.trans kept⟩
    | breakLoop | continueLoop | returned => exact ⟨rfl, kept⟩

private theorem loop {program : Program} {available : List DeclarationId}
    {source lowered : Body} (target : LoopTarget)
    (body : Exact program available source lowered) :
    Exact program available (.forIn target (.read (.bound operandSlot)) source)
      (.forIn target (.read (.bound operandSlot)) lowered) := by
  intro state free
  let operand := denote (.read (.bound operandSlot)) state
  have kept : (finishState operand).slots = state.slots := (atomScope (.bound operandVisible) state).2
  rw [denoteBody.eq_def program available (.forIn _ _ source),
    denoteBody.eq_def program available (.forIn _ _ lowered)]
  change denoteForIn target (denoteBody program available source) operand =
    denoteForIn target (denoteBody program available lowered) operand ∧ _
  obtain ⟨equal, slots⟩ := forIn_exact target _ _ body operand (fun i => (congrFun kept (temporary i)).trans (free i))
  exact ⟨equal, slots.trans kept⟩

private theorem filter {program : Program} {available : List DeclarationId}
    {yes yes' : Body} (body : Exact program available yes yes') :
    Exact program available (.branch (.read (.bound operandSlot)) yes (.total (.atomic .pass)))
      (.branch (.read (.bound operandSlot)) yes' (.total (.atomic .pass))) := by
  intro state free
  let operand := denote (.read (.bound operandSlot)) state
  have kept : (finishState operand).slots = state.slots := (atomScope (.bound operandVisible) state).2
  rw [denoteBody.eq_def program available (.branch _ yes _),
    denoteBody.eq_def program available (.branch _ yes' _)]
  let branch := fun code => Outcome.resume (Outcome.resume operand truth) (fun flag next =>
    if flag then denoteBody program available code next
    else denoteBody program available (.total (.atomic .pass)) next)
  change branch yes = branch yes' ∧ (finishState (branch yes)).slots = state.slots
  dsimp only [branch]
  cases operandRun : operand with
  | error =>
    rw [operandRun] at kept
    exact ⟨rfl, kept⟩
  | ok value next =>
    rw [operandRun] at kept
    simp only [Outcome.resume]
    have tested := truth_finishState value next
    cases testRun : truth value next with
    | error =>
      rw [testRun] at tested
      exact ⟨rfl, (congrArg State.slots tested).trans kept⟩
    | ok flag final =>
      rw [testRun] at tested
      have slots := (congrArg State.slots tested).trans kept
      cases flag with
      | false =>
        refine ⟨rfl, ?_⟩
        change (finishState (denoteBody program available (.total (.atomic .pass)) final)).slots = _
        rw [denoteBody]
        exact slots
      | true =>
        obtain ⟨equal, after⟩ := body final (fun i => (congrFun slots (temporary i)).trans (free i))
        exact ⟨equal, after.trans slots⟩

private theorem append {program : Program} {available : List DeclarationId} :
    Exact program available appendResult appendResult := by
  intro state _
  refine ⟨rfl, ?_⟩
  rw [appendResult, denoteBody]
  let action : Meaning Value := denote (.append (.read (.bound resultSlot)) (.read (.bound operandSlot)))
  have kept := (atomScope (.append (.bound resultVisible) (.bound operandVisible)) state).2
  change (finishState (Outcome.resume
    (denoteExpr program available (.atom (.append (.read (.bound resultSlot)) (.read (.bound operandSlot)))) state)
      fun _ => pure Flow.next)).slots = _
  unfold denoteExpr
  rw [Lowering.denoteExprWith.eq_def]
  change (finishState (Outcome.resume (action state) fun _ => pure Flow.next)).slots = _
  change (finishState (action state)).slots = _ at kept
  cases ran : action state <;> rw [ran] at kept <;> simpa only [ran, Outcome.resume, finishState, pure, EStateM.pure] using kept

private theorem put {program : Program} {available : List DeclarationId} :
    Exact program available putResult putResult := by
  intro state _
  refine ⟨rfl, ?_⟩
  rw [putResult, denoteBody]
  let stmt : Stmt := .setIndex (.read (.bound resultSlot)) (.read (.bound keySlot)) (.read (.bound operandSlot))
  have scope : KeepsScope (denote stmt) := by
    exact scopeBind (atomScope (.bound operandVisible)) fun value =>
      scopeBind (atomScope (.bound resultVisible)) fun receiver =>
        scopeBind (atomScope (.bound keyVisible)) fun key => writeIndexScope receiver key value
  change (finishState (Outcome.resume (denote stmt state) fun () => pure Flow.next)).slots = _
  have kept := (scope state).2
  cases ran : denote stmt state with
  | error => rw [ran] at kept; exact kept
  | ok unitValue next =>
    cases unitValue
    rw [ran] at kept
    exact kept

private theorem result {program : Program} {available : List DeclarationId} :
    Exact program available returnResult returnResult := by
  intro state _
  refine ⟨rfl, ?_⟩
  rw [returnResult, denoteBody]
  let action : Meaning Value := denote (.read (.bound resultSlot))
  have kept := (atomScope (.bound resultVisible) state).2
  change (finishState (Outcome.resume
    (denoteExpr program available (.atom (.read (.bound resultSlot))) state)
      fun value => pure (Flow.returned value))).slots = _
  unfold denoteExpr
  rw [Lowering.denoteExprWith.eq_def]
  change (finishState (Outcome.resume (action state) fun value => pure (Flow.returned value))).slots = _
  change (finishState (action state)).slots = _ at kept
  cases ran : action state <;> rw [ran] at kept <;> simpa only [ran, Outcome.resume, finishState, pure, EStateM.pure] using kept

private theorem allocate_free (locals : List Binding)
    (safe : ∀ name ∈ locals, ¬ Scratch 0 name) (state : State) (free : ScratchFree state) :
    ScratchFree (locals.foldl State.allocateSlot state) := by
  induction locals generalizing state with
  | nil => exact free
  | cons name rest ih =>
    apply ih (fun n h => safe n (List.mem_cons_of_mem _ h))
    intro index
    have distinct : temporary index ≠ name :=
      fun h => safe name (by simp) ⟨index, Nat.zero_le _, h.symm⟩
    simp [State.allocateSlot, distinct, free index]

private theorem scopeBody {program : Program} {available : List DeclarationId}
    {source lowered : Body} (target : Binding) (locals : List Binding)
    (safe : ∀ name ∈ locals, ¬ Scratch 0 name) (body : Exact program available source lowered) :
    Exact program available (.assignScoped target locals source) (.assignScoped target locals lowered) := by
  intro state free
  obtain ⟨equal, _⟩ := body _ (allocate_free locals safe state free)
  rw [denoteBody.eq_def program available (.assignScoped _ _ source),
    denoteBody.eq_def program available (.assignScoped _ _ lowered)]
  let out := denoteBody program available source (locals.foldl State.allocateSlot state)
  change completeCall state (some target) out =
    completeCall state (some target)
      (denoteBody program available lowered (locals.foldl State.allocateSlot state)) ∧ _
  refine ⟨congrArg (completeCall state (some target)) equal, ?_⟩
  change (finishState (completeCall state (some target) out)).slots = _
  cases out with
  | error => rfl
  | ok flow next =>
    change ((restoreCaller state next).write target (callValue flow)).slots = _
    exact write_slots _ _ _

private theorem tail {program : Program} {available : List DeclarationId} {Yield : Type}
    (start : Nat) (clauses : Tail Yield) (operands : Yield → List Languages.Starlark.Functions.Lowering.Expr)
    (source lowered : Yield → Body)
    (emit : ∀ value, (∀ expr ∈ operands value, Admitted expr) → Exact program available (source value) (lowered value))
    (admitted : ∀ expr ∈ clauses.operandsWith operands, Admitted expr) :
    Exact program available (clauses.compileWith Body.assignExpr source)
      (clauses.compileWith (stageLowered start) lowered) := by
  induction clauses with
  | yield value => exact emit value admitted
  | filter test rest ih =>
    exact seq (stage (admitted test (by simp [Tail.operandsWith])) operandSlot start)
      (filter (ih fun expr member => admitted expr (List.mem_cons_of_mem _ member)))
  | forIn target iterable rest ih =>
    exact seq (stage (admitted iterable (by simp [Tail.operandsWith])) operandSlot start)
      (loop target (ih fun expr member => admitted expr (List.mem_cons_of_mem _ member)))

theorem clauses_exact {program : Program} {available : List DeclarationId} {Yield Operand : Type}
    (clauses : Tail Yield Operand) {sourceHead loweredHead : Body}
    (source lowered : (operand : Operand) → operand ∈ clauses.clauseOperands → Body)
    (head : Exact program available sourceHead loweredHead)
    (related : ∀ operand member, Exact program available (source operand member) (lowered operand member)) :
    Exact program available (clauses.compileClauses sourceHead source) (clauses.compileClauses loweredHead lowered) := by
  induction clauses with
  | yield value => exact head
  | filter test rest ih =>
    exact seq (related test (by simp [Tail.clauseOperands]))
      (filter (ih _ _ (fun operand member => related operand (List.mem_cons_of_mem _ member))))
  | forIn target iterable rest ih =>
    exact seq (related iterable (by simp [Tail.clauseOperands]))
      (loop target (ih _ _ (fun operand member => related operand (List.mem_cons_of_mem _ member))))

theorem scopedBodies_exact {program : Program} {available : List DeclarationId}
    (target : Binding) (privateSlots locals : List Binding) (first : LoopTarget)
    {initial initial' iterable iterable' source lowered : Body}
    (initialEq : Exact program available initial initial') (outer : Exact program available iterable iterable')
    (privateSafe : ∀ name ∈ privateSlots, ¬ Scratch 0 name)
    (localSafe : ∀ name ∈ locals, ¬ Scratch 0 name)
    (rest : Exact program available source lowered) :
    Exact program available (compileScopedWith target privateSlots locals first initial iterable source)
      (compileScopedWith target privateSlots locals first initial' iterable' lowered) := by
  have reserved : ∀ name ∈ resultSlot :: operandSlot :: privateSlots, ¬ Scratch 0 name := by
    intro name member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact resultVisible
    · exact operandVisible
    · exact privateSafe _ member
  exact scopeBody target _ reserved
    (seq initialEq (seq outer (seq (scopeBody resultSlot locals localSafe (seq (loop first rest) result)) result)))

theorem appendYield_exact {program : Program} {available : List DeclarationId}
    {element element' : Body} (related : Exact program available element element') :
    Exact program available (appendYield element) (appendYield element') :=
  seq related append

theorem putYield_exact {program : Program} {available : List DeclarationId}
    {key key' value value' : Body}
    (keys : Exact program available key key') (values : Exact program available value value') :
    Exact program available (putYield key value) (putYield key' value') :=
  seq keys (seq values put)

theorem listYield_exact {program : Program} {available : List DeclarationId}
    {value : Languages.Starlark.Functions.Lowering.Expr} (admitted : Admitted value) (start : Nat) :
    Exact program available (listYield Body.assignExpr value) (listYield (stageLowered start) value) :=
  appendYield_exact (stage admitted operandSlot start)

theorem dictYield_exact {program : Program} {available : List DeclarationId}
    {key value : Languages.Starlark.Functions.Lowering.Expr}
    (keyAdmitted : Admitted key) (valueAdmitted : Admitted value) (start : Nat) :
    Exact program available (dictYield Body.assignExpr (key, value)) (dictYield (stageLowered start) (key, value)) :=
  putYield_exact (stage keyAdmitted keySlot start) (stage valueAdmitted operandSlot start)

theorem list_exact {program : Program} {available : List DeclarationId}
    (comp : ListComp) (target : Binding) (start : Nat)
    (outer : Admitted comp.iterable) (inner : ∀ expr ∈ comp.rest.operands, Admitted expr)
    (locals : ∀ name ∈ comp.locals, ¬ Scratch 0 name) :
    Exact program available (comp.body target) (comp.lower target start) := by
  have rest := tail (program := program) (available := available) start comp.rest (fun value => [value])
    (listYield Body.assignExpr) (listYield (stageLowered start))
    (fun value admit => listYield_exact (admit value (by simp)) start) inner
  exact scopedBodies_exact target [] comp.locals comp.target
    (stage (.atom (.list .empty)) resultSlot start) (stage outer operandSlot start) (by simp) locals rest

theorem dict_exact {program : Program} {available : List DeclarationId}
    (comp : DictComp) (target : Binding) (start : Nat)
    (outer : Admitted comp.iterable) (inner : ∀ expr ∈ comp.operands, Admitted expr)
    (locals : ∀ name ∈ comp.locals, ¬ Scratch 0 name) :
    Exact program available (comp.body target) (comp.lower target start) := by
  have rest := tail (program := program) (available := available) start comp.rest
    (fun (key, value) => [key, value]) (dictYield Body.assignExpr) (dictYield (stageLowered start))
    (fun (key, value) admit => dictYield_exact (admit key (by simp)) (admit value (by simp)) start) inner
  exact scopedBodies_exact target [keySlot] comp.locals comp.target
    (stage (.atom (.dict .noEntries)) resultSlot start) (stage outer operandSlot start)
    (by simpa using keyVisible) locals rest



theorem lower_preserves (program : Program) (available : List DeclarationId)
    (comp : ListComp) (target : Binding) (state : State) (start : Nat)
    (outer : Admitted comp.iterable) (inner : ∀ expr ∈ comp.rest.operands, Admitted expr)
    (locals : ∀ name ∈ comp.locals, ¬ Scratch 0 name) (free : ScratchFree state) :
    denoteBody program available (comp.lower target start) state =
      denoteBody program available (comp.body target) state :=
  ((list_exact comp target start outer inner locals) state free).1.symm

theorem dict_lower_preserves (program : Program) (available : List DeclarationId)
    (comp : DictComp) (target : Binding) (state : State) (start : Nat)
    (outer : Admitted comp.iterable) (inner : ∀ expr ∈ comp.operands, Admitted expr)
    (locals : ∀ name ∈ comp.locals, ¬ Scratch 0 name) (free : ScratchFree state) :
    denoteBody program available (comp.lower target start) state =
      denoteBody program available (comp.body target) state :=
  ((dict_exact comp target start outer inner locals) state free).1.symm

end Silmaril.Proofs.Languages.Starlark.Functions.Comprehensions

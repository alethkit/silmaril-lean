module

public import Silmaril.Proofs.Languages.Starlark.Functions.Comprehensions.Lowering
public import Silmaril.Languages.Starlark.Functions.Comprehensions.Expression.Source.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Comprehensions

open Silmaril.Languages.Starlark (Binding LogicalOp)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Comprehensions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration
open Silmaril.Proofs.Languages.Starlark.Functions.Lowering
  (atomScope write_slots KeepsScope scopeBind scopePure actionInsertDisplayEntry indexAction)

private abbrev Agrees (program : Program) (available : List DeclarationId) (first second : Body) :=
  ∀ state, ScratchFree state →
    denoteBody program available first state = denoteBody program available second state

private theorem sequenceDenotation (program : Program) (available : List DeclarationId)
    (first rest : Body) (state : State) :
    denoteBody program available (.seq first rest) state =
      Outcome.resume (denoteBody program available first state) fun
      | .next => denoteBody program available rest
      | signal => pure signal := by rw [denoteBody]; rfl

private theorem seq_agrees {program : Program} {available : List DeclarationId}
    {first first' rest rest' : Body}
    (before : Exact program available first first') (after : Agrees program available rest rest') :
    Agrees program available (.seq first rest) (.seq first' rest') := by
  intro state free
  obtain ⟨equal, slots⟩ := before state free
  rw [sequenceDenotation, sequenceDenotation, ← equal]
  cases ran : denoteBody program available first state with
  | error => rfl
  | ok flow next =>
    cases flow with
    | next =>
      rw [ran] at slots
      exact after next (fun index => (congrFun slots (temporary index)).trans (free index))
    | breakLoop | continueLoop | returned => rfl

private theorem scope_exact {program : Program} {available : List DeclarationId}
    {first second : Body} (target : Binding) (inside : Agrees program available first second) :
    Exact program available (.assignScoped target [] first) (.assignScoped target [] second) := by
  intro state free
  rw [denoteBody.eq_def program available (.assignScoped _ _ first),
    denoteBody.eq_def program available (.assignScoped _ _ second)]
  let out := denoteBody program available first state
  change completeCall state (some target) out =
    completeCall state (some target) (denoteBody program available second state) ∧
    (finishState (completeCall state (some target) out)).slots = state.slots
  refine ⟨congrArg (completeCall state (some target)) (inside state free), ?_⟩
  cases out with
  | error => rfl
  | ok flow next =>
    change ((restoreCaller state next).write target (callValue flow)).slots = _
    exact write_slots _ _ _

private theorem branchDenotation (program : Program) (available : List DeclarationId)
    (test : Silmaril.Languages.Starlark.Lists.Expr) (yes no : Body) (state : State) :
    denoteBody program available (.branch test yes no) state =
      Outcome.resume (Outcome.resume (denote test state) truth) (fun flag next =>
        if flag then denoteBody program available yes next else denoteBody program available no next) := by
  rw [denoteBody] <;> rfl

private theorem branch_agrees {program : Program} {available : List DeclarationId}
    {yes no yes' no' : Body} (selected : Agrees program available yes yes')
    (skipped : Agrees program available no no') :
    Agrees program available (.branch (readSaved expressionSlot) yes no)
      (.branch (readSaved expressionSlot) yes' no') := by
  intro state free
  have visible : ¬ Scratch 0 expressionSlot := by
    rintro ⟨index, _, equal⟩
    have := congrArg Binding.scope equal
    contradiction
  have scope := (atomScope (.bound visible) state).2
  change (finishState (denote (readSaved expressionSlot) state)).slots = state.slots at scope
  rw [branchDenotation, branchDenotation]
  cases ran : denote (readSaved expressionSlot) state with
  | error => rfl
  | ok value next =>
    rw [ran] at scope
    simp only [Outcome.resume]
    have tested := truth_finishState value next
    cases checked : truth value next with
    | error => rfl
    | ok flag final =>
      rw [checked] at tested
      have kept := (congrArg State.slots tested).trans scope
      cases flag with
      | false => exact skipped final (fun index => (congrFun kept (temporary index)).trans (free index))
      | true => exact selected final (fun index => (congrFun kept (temporary index)).trans (free index))

private theorem argument_agrees {program : Program} {available : List DeclarationId} {α : Type}
    (operands : List α) (source lowered : α → Binding → Body)
    (related : ∀ item ∈ operands, ∀ target, Exact program available (source item target) (lowered item target))
    (index : Nat) (dispatch : List Silmaril.Languages.Starlark.Lists.Expr → Body) :
    Agrees program available (stageArguments index (operands.map source) dispatch)
      (stageArguments index (operands.map lowered) dispatch) := by
  induction operands generalizing index dispatch with
  | nil => exact fun _ _ => rfl
  | cons item rest ih =>
    exact seq_agrees (related item (by simp) _)
      (ih (fun item member => related item (List.mem_cons_of_mem _ member)) _ _)

private theorem savedReadScope (slot : Binding) :
    KeepsScope (fun state : State => state.read (.bound slot)) := by
  intro state
  simp only [State.read]
  cases state.bindingValue slot <;> exact ⟨rfl, rfl⟩

private theorem insert_exact {program : Program} {available : List DeclarationId} :
    Exact program available (.insertDictEntry expressionSlot (argumentSlot 0) (argumentSlot 1))
      (.insertDictEntry expressionSlot (argumentSlot 0) (argumentSlot 1)) := by
  intro state _
  refine ⟨rfl, ?_⟩
  rw [denoteBody]
  have keep : KeepsScope (insertDictEntry expressionSlot (argumentSlot 0) (argumentSlot 1)) :=
    scopeBind (savedReadScope expressionSlot) fun receiver =>
      scopeBind (savedReadScope (argumentSlot 0)) fun key =>
        scopeBind (savedReadScope (argumentSlot 1)) fun value =>
          scopeBind (actionInsertDisplayEntry receiver key value).2 fun () => scopePure Flow.next
  exact (keep state).2

private theorem entries_agree {program : Program} {available : List DeclarationId} {α : Type}
    (entries : List α) (source lowered : α → (Binding → Body) × (Binding → Body))
    (keys : ∀ item ∈ entries, Exact program available
      ((source item).1 (argumentSlot 0)) ((lowered item).1 (argumentSlot 0)))
    (values : ∀ item ∈ entries, Exact program available
      ((source item).2 (argumentSlot 1)) ((lowered item).2 (argumentSlot 1))) (rest : Body) :
    Agrees program available
      ((entries.map source).foldr (fun (key, value) tail => stageDisplayEntry key value tail) rest)
      ((entries.map lowered).foldr (fun (key, value) tail => stageDisplayEntry key value tail) rest) := by
  induction entries with
  | nil => exact fun _ _ => rfl
  | cons entry entries ih =>
    exact seq_agrees (keys entry (by simp)) (seq_agrees (values entry (by simp))
      (seq_agrees insert_exact (ih
        (fun item member => keys item (List.mem_cons_of_mem _ member))
        (fun item member => values item (List.mem_cons_of_mem _ member)))))

theorem expression_exact (program : Program) (available : List DeclarationId)
    (expr : Expression) (admitted : expr.Admitted) (target : Binding) (start : Nat) :
    Exact program available (expr.body target) (expr.lower target start) := by
  unfold Expression.body Expression.lower
  rw [Expression.compile.eq_def directStages expr, Expression.compile.eq_def (loweredStages start) expr]
  cases admitted with
  | plain admitted => exact stage admitted target start
  | list outer inner locals => exact list_exact _ target start outer inner locals
  | dict outer inner locals => exact dict_exact _ target start outer inner locals
  | @listClauses locals first iterable rest outer clauses head safe =>
    apply scopedBodies_exact target [] locals first (stage (.atom (.list .empty)) resultSlot start)
      (expression_exact program available iterable outer operandSlot start) (by simp) safe
    apply clauses_exact
    · exact listYield_exact head start
    · intro operand member
      have := rest.clauseOperandSize member
      exact expression_exact program available operand (clauses operand member) operandSlot start
  | @dictClauses locals first iterable rest outer clauses key value safe =>
    apply scopedBodies_exact target [keySlot] locals first (stage (.atom (.dict .noEntries)) resultSlot start)
      (expression_exact program available iterable outer operandSlot start) (by simpa using keyVisible) safe
    apply clauses_exact
    · exact dictYield_exact key value start
    · intro operand member
      have := rest.clauseOperandSize member
      exact expression_exact program available operand (clauses operand member) operandSlot start
  | @listComprehension locals first iterable rest outer clauses head safe =>
    apply scopedBodies_exact target [] locals first (stage (.atom (.list .empty)) resultSlot start)
      (expression_exact program available iterable outer operandSlot start) (by simp) safe
    apply clauses_exact
    · have := rest.headValueSize
      exact appendYield_exact (expression_exact program available rest.headValue head operandSlot start)
    · intro operand member
      have := rest.clauseOperandSize member
      exact expression_exact program available operand (clauses operand member) operandSlot start
  | @dictComprehension locals first iterable rest outer clauses key value safe =>
    apply scopedBodies_exact target [keySlot] locals first (stage (.atom (.dict .noEntries)) resultSlot start)
      (expression_exact program available iterable outer operandSlot start) (by simpa using keyVisible) safe
    apply clauses_exact
    · have headSize := rest.headValueSize
      have pairSize : sizeOf rest.headValue = 1 + sizeOf rest.headValue.1 + sizeOf rest.headValue.2 := by
        cases rest.headValue <;> rfl
      exact putYield_exact (expression_exact program available rest.headValue.1 key keySlot start)
        (expression_exact program available rest.headValue.2 value operandSlot start)
    · intro operand member
      have := rest.clauseOperandSize member
      exact expression_exact program available operand (clauses operand member) operandSlot start
  | listDisplay elements | tupleDisplay elements =>
    unfold compileSequence
    apply scope_exact target
    apply argument_agrees
    intro item _ destination
    have := List.sizeOf_lt_of_mem item.property
    exact expression_exact program available item.val (elements _ item.property) destination start
  | dictDisplay keys values =>
    unfold compileDictDisplay
    apply scope_exact target
    apply seq_agrees
    · intro state free
      exact ⟨rfl, (stage (.atom (.dict .noEntries)) expressionSlot start state free).2⟩
    apply entries_agree
    · intro item _
      obtain ⟨⟨key, value⟩, member⟩ := item
      have := (Lowering.entrySize member).1
      exact expression_exact program available key (keys _ member) (argumentSlot 0) start
    · intro item _
      obtain ⟨⟨key, value⟩, member⟩ := item
      have := (Lowering.entrySize member).2
      exact expression_exact program available value (values _ member) (argumentSlot 1) start
  | index receiver subscript =>
    unfold compileIndex
    apply scope_exact target
    exact seq_agrees (expression_exact program available _ receiver (argumentSlot 0) start)
      (seq_agrees (expression_exact program available _ subscript (argumentSlot 1) start) (fun _ _ => rfl))
  | slice operands =>
    unfold compileSequence
    apply scope_exact target
    apply argument_agrees
    intro item _ destination
    have := Silmaril.Languages.Starlark.Functions.Comprehensions.sliceOperandSize item.property
    exact expression_exact program available item.val (operands _ item.property) destination start
  | callPos callee arguments =>
    unfold compileCall
    apply scope_exact target
    apply seq_agrees (stage callee (argumentSlot 0) start)
    apply argument_agrees
    intro item _ destination
    have := List.sizeOf_lt_of_mem item.property
    exact expression_exact program available item.val (arguments _ item.property) destination start
  | @call callee positional keywords star starStar calleeAdmitted arguments =>
    unfold compileCall
    apply scope_exact target
    apply seq_agrees (expression_exact program available callee calleeAdmitted (argumentSlot 0) start)
    apply argument_agrees
    intro item _ destination
    have := callOperandSize callee positional keywords star starStar item.property
    exact expression_exact program available item.val (arguments _ item.property) destination start
  | branch test yes no =>
    apply scope_exact target
    apply seq_agrees (expression_exact program available _ test expressionSlot start)
    apply branch_agrees
    · exact seq_agrees (expression_exact program available _ yes expressionSlot start) (fun _ _ => rfl)
    · exact seq_agrees (expression_exact program available _ no expressionSlot start) (fun _ _ => rfl)
  | @logical op left right leftAdmitted rightAdmitted =>
    apply scope_exact target
    apply seq_agrees (expression_exact program available _ leftAdmitted expressionSlot start)
    have rightEq := seq_agrees (expression_exact program available right rightAdmitted expressionSlot start)
      (rest := returnSaved expressionSlot) (rest' := returnSaved expressionSlot) (fun _ _ => rfl)
    cases op with
    | and => exact branch_agrees rightEq (fun _ _ => rfl)
    | or => exact branch_agrees (fun _ _ => rfl) rightEq
termination_by sizeOf expr
decreasing_by all_goals first | assumption | (simp_wf; omega)

theorem return_exact (program : Program) (available : List DeclarationId)
    (expr : Expression) (admitted : expr.Admitted) (state : State) (free : ScratchFree state) (start : Nat) :
    denoteBody program available (expr.returnCode (loweredStages start)) state =
      denoteBody program available (expr.returnCode directStages) state :=
  (seq_agrees (expression_exact program available expr admitted expressionSlot start)
    (rest := returnSaved expressionSlot) (rest' := returnSaved expressionSlot) (fun _ _ => rfl) state free).symm

theorem assign_target_exact (program : Program) (available : List DeclarationId)
    (expr : Expression) (admitted : expr.Admitted) (target : LoopTarget)
    (state : State) (free : ScratchFree state) (start : Nat) :
    denoteBody program available (expr.assignTargetCode target (loweredStages start)) state =
      denoteBody program available (expr.assignTargetCode target directStages) state := by
  unfold Expression.assignTargetCode
  rw [denoteBody.eq_def program available (.assignTargetScoped target _),
    denoteBody.eq_def program available (.assignTargetScoped target _)]
  exact congrArg (completeTargetAssignment state target) (return_exact program available expr admitted state free start)

theorem set_index_exact (program : Program) (available : List DeclarationId)
    (receiver subscript rhs : Expression) (receiverAdmitted : receiver.Admitted)
    (subscriptAdmitted : subscript.Admitted) (rhsAdmitted : rhs.Admitted)
    (state : State) (free : ScratchFree state) (start : Nat) :
    denoteBody program available (setIndexCode receiver subscript rhs (loweredStages start)) state =
      denoteBody program available (setIndexCode receiver subscript rhs directStages) state := by
  unfold setIndexCode
  rw [denoteBody.eq_def program available (.evalScoped _),
    denoteBody.eq_def program available (.evalScoped _)]
  apply congrArg (completeCall state none)
  symm
  exact seq_agrees (expression_exact program available rhs rhsAdmitted (argumentSlot 0) start)
    (seq_agrees (expression_exact program available receiver receiverAdmitted (argumentSlot 1) start)
      (seq_agrees (expression_exact program available subscript subscriptAdmitted (argumentSlot 2) start)
        (fun _ _ => rfl))) state free

theorem set_index_rhs_failure (program : Program) (available : List DeclarationId)
    (receiver subscript rhs : Expression) (stages : ExpressionStages) (state failed : State) (error : Error)
    (ran : denoteBody program available (rhs.compile stages (argumentSlot 0)) state = .error error failed) :
    denoteBody program available (setIndexCode receiver subscript rhs stages) state =
      .error error (restoreCaller state failed) := by
  rw [setIndexCode, denoteBody]
  change completeCall state none (denoteBody program available (.seq _ _) state) = _
  rw [sequenceDenotation, ran]
  rfl

private theorem assign_atom_exact {program : Program} {available : List DeclarationId}
    (target : Binding) {code : Silmaril.Languages.Starlark.Lists.Expr}
    (keep : KeepsScope (denote code)) :
    Exact program available (.assignExpr target (.atom code)) (.assignExpr target (.atom code)) := by
  intro state _
  refine ⟨rfl, ?_⟩
  rw [denoteBody]
  change (finishState (Outcome.resume (denoteExpr program available (.atom code) state)
    (fun value next => .ok Flow.next (next.write target value)))).slots = state.slots
  unfold denoteExpr
  rw [denoteExprWith.eq_def]
  change (finishState (Outcome.resume (denote code state)
    (fun value next => .ok Flow.next (next.write target value)))).slots = state.slots
  have slots := (keep state).2
  cases ran : denote code state with
  | error =>
    rw [ran] at slots
    exact slots
  | ok value next =>
    rw [ran] at slots
    exact (write_slots next target value).trans slots

theorem add_index_exact (program : Program) (available : List DeclarationId)
    (receiver subscript rhs : Expression) (receiverAdmitted : receiver.Admitted)
    (subscriptAdmitted : subscript.Admitted) (rhsAdmitted : rhs.Admitted)
    (state : State) (free : ScratchFree state) (start : Nat) :
    denoteBody program available (addIndexCode receiver subscript rhs (loweredStages start)) state =
      denoteBody program available (addIndexCode receiver subscript rhs directStages) state := by
  have old : Exact program available readIndexForAdd readIndexForAdd := by
    apply assign_atom_exact
    exact scopeBind (savedReadScope (argumentSlot 0)) fun receiver =>
      scopeBind (savedReadScope (argumentSlot 1)) fun index => (indexAction receiver index).2
  unfold addIndexCode
  rw [denoteBody.eq_def program available (.evalScoped _),
    denoteBody.eq_def program available (.evalScoped _)]
  apply congrArg (completeCall state none)
  symm
  exact seq_agrees (expression_exact program available receiver receiverAdmitted (argumentSlot 0) start)
    (seq_agrees (expression_exact program available subscript subscriptAdmitted (argumentSlot 1) start)
      (seq_agrees old (seq_agrees (expression_exact program available rhs rhsAdmitted (argumentSlot 3) start)
        (fun _ _ => rfl)))) state free

theorem add_index_after_target (program : Program) (available : List DeclarationId)
    (receiver subscript rhs : Expression) (stages : ExpressionStages) (state afterReceiver afterIndex : State)
    (recv : denoteBody program available (receiver.compile stages (argumentSlot 0)) state =
      .ok .next afterReceiver)
    (index : denoteBody program available (subscript.compile stages (argumentSlot 1)) afterReceiver =
      .ok .next afterIndex) :
    denoteBody program available (addIndexCode receiver subscript rhs stages) state =
      completeCall state none (Outcome.resume (denoteBody program available readIndexForAdd afterIndex) fun
        | .next => denoteBody program available (.seq (rhs.compile stages (argumentSlot 3)) writeIndexSum)
        | signal => pure signal) := by
  rw [addIndexCode, denoteBody]
  change completeCall state none (denoteBody program available (.seq _ _) state) = _
  rw [sequenceDenotation, recv]
  change completeCall state none (denoteBody program available (.seq _ _) afterReceiver) = _
  rw [sequenceDenotation, index]
  change completeCall state none (denoteBody program available (.seq _ _) afterIndex) = _
  rw [sequenceDenotation]
  rfl

theorem add_name_exact (program : Program) (available : List DeclarationId)
    (target : Binding) (rhs : Expression) (admitted : rhs.Admitted)
    (state : State) (free : ScratchFree state) (start : Nat) :
    denoteBody program available (addNameCode target rhs (loweredStages start)) state =
      denoteBody program available (addNameCode target rhs directStages) state := by
  unfold addNameCode
  rw [denoteBody.eq_def program available (.assignScoped _ _ _),
    denoteBody.eq_def program available (.assignScoped _ _ _)]
  apply congrArg (completeCall state (some target))
  symm
  exact seq_agrees (assign_atom_exact (argumentSlot 0) (code := readSaved target) (savedReadScope target))
    (seq_agrees (expression_exact program available rhs admitted (argumentSlot 1) start)
      (fun _ _ => rfl)) state free

theorem definition_defaults_exact (program : Program) (available : List DeclarationId)
    (target : Binding) (id : DeclarationId) (defaults : List (Binding × Expression))
    (admitted : ∀ item ∈ defaults, item.2.Admitted) (start : Nat) :
    Exact program available (definitionWithDefaults directStages target id defaults)
      (definitionWithDefaults (loweredStages start) target id defaults) := by
  unfold definitionWithDefaults
  apply scope_exact target
  induction defaults with
  | nil => exact fun _ _ => rfl
  | cons item rest ih =>
    exact seq_agrees
      (expression_exact program available item.2 (admitted item (by simp)) (defaultSlot item.1) start)
      (ih (fun default member => admitted default (List.mem_cons_of_mem _ member)))

theorem definition_default_failure (program : Program) (available : List DeclarationId)
    (stages : ExpressionStages) (target parameter : Binding) (id : DeclarationId) (expr : Expression)
    (rest : List (Binding × Expression)) (state failed : State) (error : Error)
    (ran : denoteBody program available (expr.compile stages (defaultSlot parameter)) state =
      .error error failed) :
    denoteBody program available (definitionWithDefaults stages target id ((parameter, expr) :: rest)) state =
      .error error (restoreCaller state failed) := by
  rw [definitionWithDefaults, denoteBody]
  change completeCall state (some target)
    (denoteBody program available (.seq _ _) state) = _
  rw [sequenceDenotation, ran]
  rfl

theorem logical_skips (program : Program) (available : List DeclarationId) (stages : ExpressionStages)
    (op : LogicalOp) (left right : Expression) (target : Binding) (state next : State)
    (value : Value) (flag : Bool)
    (ran : denoteBody program available (left.compile stages expressionSlot) state = .ok .next next)
    (saved : denote (readSaved expressionSlot) next = .ok value next)
    (tested : truth value next = .ok flag next)
    (skip : (if op = .and then flag else !flag) = false) :
    denoteBody program available ((Expression.logical op left right).compile stages target) state =
      .ok .next ((restoreCaller state next).write target value) := by
  rw [Expression.compile.eq_def stages (.logical op left right), denoteBody]
  change completeCall state (some target) (denoteBody program available (.seq _ _) state) = _
  rw [sequenceDenotation, ran]
  cases op <;> cases flag <;> simp at skip
  all_goals
    simp only [Outcome.resume]
    rw [branchDenotation, saved]
    simp only [Outcome.resume, tested, Bool.false_eq_true, ite_false, ite_true]
    rw [returnSaved, denoteBody]
    change completeCall state (some target)
      (Outcome.resume (denoteExpr program available (.atom (readSaved expressionSlot)) next)
        (fun result => pure (.returned result))) = _
    unfold denoteExpr
    rw [denoteExprWith.eq_def]
    change completeCall state (some target) (Outcome.resume (denote (readSaved expressionSlot) next)
      (fun result => pure (.returned result))) = _
    rw [saved]
    rfl

theorem conditional_selects (program : Program) (available : List DeclarationId)
    (stages : ExpressionStages) (test yes no : Expression) (target : Binding) (state next : State)
    (value : Value) (flag : Bool)
    (ran : denoteBody program available (test.compile stages expressionSlot) state = .ok .next next)
    (saved : denote (readSaved expressionSlot) next = .ok value next)
    (tested : truth value next = .ok flag next) :
    denoteBody program available ((Expression.branch test yes no).compile stages target) state =
      completeCall state (some target)
        (denoteBody program available
          (.seq ((if flag then yes else no).compile stages expressionSlot) (returnSaved expressionSlot)) next) := by
  rw [Expression.compile.eq_def stages (.branch test yes no), denoteBody]
  change completeCall state (some target) (denoteBody program available (.seq _ _) state) = _
  rw [sequenceDenotation, ran]
  simp only [Outcome.resume]
  rw [branchDenotation, saved]
  simp only [Outcome.resume, tested]
  cases flag <;> rfl

theorem callee_failure (program : Program) (available : List DeclarationId) (stages : ExpressionStages)
    (callee : Silmaril.Languages.Starlark.Functions.Lowering.Expr) (arguments : List Expression)
    (target : Binding) (state stopped : State) (error : Error)
    (failed : denoteBody program available (stages.plain (argumentSlot 0) callee) state = .error error stopped) :
    denoteBody program available ((Expression.callPos callee arguments).compile stages target) state =
      .error error (restoreCaller state stopped) := by
  rw [Expression.compile.eq_def stages (.callPos callee arguments)]
  dsimp only
  unfold compileCall
  rw [denoteBody]
  change completeCall state (some target) (denoteBody program available (.seq _ _) state) = _
  rw [sequenceDenotation, failed]
  rfl

theorem call_order (program : Program) (available : List DeclarationId) (target : Binding)
    (callee : Body) (shape : ArgumentShape) (operands : List (Binding → Body)) (state : State) :
    denoteBody program available (compileCall target callee shape operands) state =
      completeCall state (some target)
        (Outcome.resume (denoteBody program available callee state) fun
          | .next => denoteBody program available
              (stageArguments 1 operands fun saved =>
                .seq (.call (some expressionSlot) (readSaved (argumentSlot 0)) (fillArguments shape saved))
                  (returnSaved expressionSlot))
          | signal => pure signal) := by
  rw [compileCall, denoteBody]
  change completeCall state (some target) (denoteBody program available (.seq _ _) state) = _
  rw [sequenceDenotation] <;> rfl

theorem call_callee_failure (program : Program) (available : List DeclarationId) (stages : ExpressionStages)
    (callee : Expression) (positional : List Expression) (keywords : List (String × Expression))
    (star starStar : Option Expression) (target : Binding) (state stopped : State) (error : Error)
    (failed : denoteBody program available (callee.compile stages (argumentSlot 0)) state = .error error stopped) :
    denoteBody program available ((Expression.call callee positional keywords star starStar).compile stages target) state =
      .error error (restoreCaller state stopped) := by
  rw [Expression.compile.eq_def stages (.call callee positional keywords star starStar), call_order, failed]
  rfl

theorem argument_order (program : Program) (available : List DeclarationId) (index : Nat)
    (first : Binding → Body) (rest : List (Binding → Body))
    (dispatch : List Silmaril.Languages.Starlark.Lists.Expr → Body) (state : State) :
    denoteBody program available (stageArguments index (first :: rest) dispatch) state =
      Outcome.resume (denoteBody program available (first (argumentSlot index)) state) fun
      | .next => denoteBody program available
          (stageArguments (index + 1) rest fun saved => dispatch (readSaved (argumentSlot index) :: saved))
      | signal => pure signal :=
  sequenceDenotation _ _ _ _ _

private theorem sequenceMeaning (program : Program) (available : List DeclarationId)
    (first rest : Body) :
    denoteBody program available (.seq first rest) = fun state =>
      Outcome.resume (denoteBody program available first state) fun
      | .next => denoteBody program available rest
      | signal => pure signal :=
  funext (sequenceDenotation program available first rest)

theorem display_entry_order (program : Program) (available : List DeclarationId)
    (key value : Binding → Body) (rest : Body) (state : State) :
    denoteBody program available (stageDisplayEntry key value rest) state =
      Outcome.resume (denoteBody program available (key (argumentSlot 0)) state) fun
        | .next => fun next =>
          Outcome.resume (denoteBody program available (value (argumentSlot 1)) next) fun
            | .next => fun next =>
              Outcome.resume (denoteBody program available
                (.insertDictEntry expressionSlot (argumentSlot 0) (argumentSlot 1)) next) fun
                | .next => denoteBody program available rest
                | signal => pure signal
            | signal => pure signal
        | signal => pure signal := by
  simp only [stageDisplayEntry, sequenceMeaning] <;> rfl

theorem index_order (program : Program) (available : List DeclarationId)
    (target : Binding) (receiver subscript : Binding → Body) (state : State) :
    denoteBody program available (compileIndex target receiver subscript) state =
      completeCall state (some target)
        (Outcome.resume (denoteBody program available (receiver (argumentSlot 0)) state) fun
          | .next => fun next =>
            Outcome.resume (denoteBody program available (subscript (argumentSlot 1)) next) fun
              | .next => denoteBody program available (.returnExpr
                  (.atom (.index (readSaved (argumentSlot 0)) (readSaved (argumentSlot 1)))))
              | signal => pure signal
          | signal => pure signal) := by
  rw [compileIndex, denoteBody]
  change completeCall state (some target) (denoteBody program available (.seq _ _) state) = _
  simp only [sequenceMeaning] <;> rfl

theorem slice_order (program : Program) (available : List DeclarationId)
    (target : Binding) (receiver start stop stride : Binding → Body) (state : State) :
    let saved := [0, 1, 2, 3].map fun index => readSaved (argumentSlot index)
    let readback := denoteBody program available (.returnExpr (.atom (.slice (operandList saved))))
    let stages := [receiver (argumentSlot 0), start (argumentSlot 1),
      stop (argumentSlot 2), stride (argumentSlot 3)].map (denoteBody program available)
    let execute := stages.foldr (fun operand rest next => Outcome.resume (operand next) fun
      | .next => rest
      | signal => pure signal) readback
    denoteBody program available (compileSequence target (.slice ∘ operandList) [receiver, start, stop, stride]) state =
      completeCall state (some target) (execute state) := by
  dsimp only
  rw [compileSequence, denoteBody]
  change completeCall state (some target) (denoteBody program available (stageArguments 0 _ _) state) = _
  simp only [stageArguments, sequenceMeaning, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] <;> rfl

theorem first_iterable_failure (program : Program) (available : List DeclarationId)
    (target : Binding) (privateSlots locals : List Binding) (first : LoopTarget)
    (initial iterable rest : Body) (state ready stopped : State) (error : Error)
    (allocated : denoteBody program available initial
      ((resultSlot :: operandSlot :: privateSlots).foldl State.allocateSlot state) = .ok .next ready)
    (failed : denoteBody program available iterable ready = .error error stopped) :
    denoteBody program available (compileScopedWith target privateSlots locals first initial iterable rest) state =
      .error error (restoreCaller state stopped) := by
  rw [compileScopedWith, denoteBody]
  change completeCall state (some target) (denoteBody program available (.seq _ _)
    ((resultSlot :: operandSlot :: privateSlots).foldl State.allocateSlot state)) = _
  rw [sequenceDenotation, allocated]
  change completeCall state (some target) (denoteBody program available (.seq _ _) ready) = _
  rw [sequenceDenotation, failed]
  rfl

theorem dict_yield_order (program : Program) (available : List DeclarationId)
    (key value : Body) (state : State) :
    denoteBody program available (putYield key value) state =
      Outcome.resume (denoteBody program available key state) fun
        | .next => fun next =>
          Outcome.resume (denoteBody program available value next) fun
            | .next => denoteBody program available putResult
            | signal => pure signal
        | signal => pure signal := by
  simp only [putYield, sequenceMeaning] <;> rfl

end Silmaril.Proofs.Languages.Starlark.Functions.Comprehensions

module

public import Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA.Defs
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Run.Thms
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA.Proofs

open RVSDG (Port Tuple Wires Origin)
open Diamond (ValueSort dataPorts sortValue read)
open Diamond.LambdaSSA (Atom Layout LayoutMatch Primitive Ref encode encodePort encodeTuple
  inputEnv instruction portCode shiftRef scheduleLayout sortCode terminatorRegion
  tuple_get_map schedule_typed schedule_eval instruction_deterministic)
open Loop.LambdaSSA.Generic (arguments arguments_read packed unpackEnv unpackRefs_match
  unpack_typed unpack_eval)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {n : Nat} {σ : Type x}
variable {graph : Graph Op regs n} {source : Fin n}

theorem binding_incoming (edge : Edge graph source) {t : Diamond.Ty Data}
    (port : Port (dataPorts regs) t) :
    (binding edge port).incoming = (graph.versions source).get port := by
  induction edge with
  | latest occurrence =>
    simp [binding, Graph.versions, Graph.column, tuple_get_map]
  | earlier edge ih =>
    simp [binding, Binding.lift, Graph.versions, tuple_get_map, ih]

theorem binding_bound (edge : Edge graph source) {t : Diamond.Ty Data}
    (port : Port (dataPorts regs) t) :
    (binding edge port).bound = (binding edge port).incoming ∨
      (binding edge port).bound = .phi edge.target := by
  induction edge with
  | @latest _ prior preds _ occurrence =>
    cases h : (prior.header preds).get port with
    | none => exact Or.inr (by simp [binding, Inputs.version, h, Edge.target])
    | some previous =>
      exact Or.inl (by simp [binding, Inputs.version, h, prior.header_reuse preds occurrence _ _ h])
  | earlier edge ih =>
    rcases ih with h | h
    · exact Or.inl (congrArg Version.lift h)
    · exact Or.inr (congrArg Version.lift h)

private theorem eval_beforeLatest {prior : Graph Op regs n} {preds : Predecessors n}
    {body : Join.Block Op regs} {i : Fin (n + 1)} (path : Path (.snoc prior preds body) i)
    (bound : i.val < n) (m : Diamond.Model.{u, v, w} Op) (input : Bank m regs) :
    (path.beforeLatest bound).eval m input = path.eval m input := by
  cases path with
  | earlier _ => rfl
  | edge _ _ => exact (Nat.lt_irrefl _ bound).elim

theorem headerBank_agrees (edge : Edge graph source) (path : Path graph source)
    (m : Diamond.Model.{u, v, w} Op) (input : Bank m regs) :
    headerBank m input edge path = some (path.eval m input) := by
  induction edge with
  | @latest _ prior preds _ occurrence =>
    obtain ⟨values, defined, _, agreed⟩ := prior.edge_agrees preds occurrence path.unlift m input
    change ((path.unlift.values m input).bind fun older => readBank (dataPorts regs)
      ((prior.header preds).read older (older.read (prior.column preds occurrence)))) = _
    rw [defined]
    simpa [Path.unlift, eval_beforeLatest] using agreed
  | earlier edge ih =>
    simpa [headerBank, Path.unlift, eval_beforeLatest] using ih path.unlift

private abbrev labels (regs : List (ValueSort Data)) (out : ValueSort Data) (n : Nat) :=
  (List.ofFn fun _ : Fin n => bankCode regs) ++ [returnCode out]

private theorem bank_label (index : Fin n) : At (labels regs out n) index.val (bankCode regs) := by
  change (labels regs out n)[index.val]? = some (bankCode regs)
  have inside : index.val < (List.ofFn fun _ : Fin n => bankCode regs).length :=
    by simp [index.isLt]
  simp [List.getElem?_append_left inside, index.isLt]

private theorem emit_bank_label (index : Fin n) :
    At (labels regs out n) index.val (PhiView.packedType (parameters regs out n index.val)) := by
  rw [parameters_inside index]
  exact bank_label index

private theorem emit_return_label :
    At (labels regs out n) n (PhiView.packedType (parameters regs out n n)) := by
  rw [parameters_return]
  change (labels regs out n)[n]? = some (returnCode out)
  simp

private theorem emit_typed {context : List (Silmaril.Ty Data)} (resolve : Resolver graph source context)
    (term : Terminator graph source out) :
    (terminatorRegion (emit resolve term)).HasType context (labels regs out n) := by
  cases term with
  | jump edge =>
    exact .br (emit_bank_label edge.target) (PhiView.packTerm_hasType (jumpArgs resolve edge))
  | ret result =>
    exact .br emit_return_label (PhiView.packTerm_hasType (returnArgs resolve result))
  | branch test onTrue onFalse _ =>
    exact .case (A := .unit) (B := .unit)
      (.var (resolve ((transfer graph source).outgoing.get test)).property)
      (.br (emit_bank_label onTrue.target) (PhiView.packTerm_hasType
        (jumpArgs (fun wire => shiftRef (resolve wire)) onTrue)))
      (.br (emit_bank_label onFalse.target) (PhiView.packTerm_hasType
        (jumpArgs (fun wire => shiftRef (resolve wire)) onFalse)))

theorem lower_hasType (program : Program graph out) :
    (lower program).HasType (bankTypes regs) [returnCode out] := by
  refine .cfg (fun _ => bankCode regs) ?_ (fun source => ?_)
  · exact .br (bank_label graph.start.1) (PhiView.packTerm_hasType (entryArgs regs))
  · exact unpack_typed _ (schedule_typed _ _ (emit_typed _ (program.terminator source)))

private theorem chosen_edge {context : List (Silmaril.Ty Data)} (resolve : Resolver graph source context)
    (term : Terminator graph source out) (m : Diamond.Model.{u, v, w} Op) (bank : Bank m regs) :
    sourceEdge resolve term (chosenLeaf resolve m bank term) =
      match term.eval m bank with
      | .inl _ => none
      | .inr edge => some edge := by
  cases term with
  | jump | ret => rfl
  | branch test _ _ _ =>
    cases h : (bank.get test).down <;> simp [sourceEdge, chosenLeaf, Terminator.eval, h]

theorem selected_edge (program : Program graph out) (m : Diamond.Model.{u, v, w} Op)
    (bank : Bank m regs) (source : Fin n) :
    occurrenceEdge program (selectedOccurrence program m bank source) =
      match (program.terminator source).eval m bank with
      | .inl _ => none
      | .inr edge => some edge := by
  unfold occurrenceEdge selectedOccurrence
  dsimp only
  have selected := chosen_edge (finalLayout graph source).resolve (program.terminator source) m bank
  cases taken : (program.terminator source).eval m bank <;> simpa [taken] using selected

theorem selected_distinct (program : Program graph out) (m : Diamond.Model.{u, v, w} Op)
    (leftBank rightBank : Bank m regs) (left right : Edge graph source)
    (leftTaken : (program.terminator source).eval m leftBank = .inr left)
    (rightTaken : (program.terminator source).eval m rightBank = .inr right)
    (differentSlots : left.slot ≠ right.slot) :
    selectedOccurrence program m leftBank source ≠ selectedOccurrence program m rightBank source := by
  intro equal
  have slots := congrArg (fun occurrence : PhiView.EdgeOcc (terminators program) =>
    (occurrenceEdge program occurrence).map Edge.slot) equal
  simp only [selected_edge, leftTaken, rightTaken, Option.map_some] at slots
  exact differentSlots (Option.some.inj slots)

private theorem pack_eval {context : List (Silmaril.Ty Data)} {types : List (Silmaril.Ty Data)}
    (args : PhiView.Arguments context types) (m : Diamond.Model.{u, v, w} Op)
    (env : Env (Atom m)) (start : σ) :
    Semantics.Tm.Eval (instruction m) env (PhiView.packTerm args) start
      (PhiView.readArguments args env) start := by
  induction types with
  | nil => exact .unit
  | cons _ _ ih => exact .pair .var (ih (fun p => args p.succ))

private theorem pack_eval_of_read {context types : List (Silmaril.Ty Data)}
    (args : PhiView.Arguments context types) (m : Diamond.Model.{u, v, w} Op)
    (env : Env (Atom m)) (start : σ) {value : Value (Atom m)}
    (reads : PhiView.readArguments args env = value) :
    Semantics.Tm.Eval (instruction m) env (PhiView.packTerm args) start value start := by
  rw [← reads]
  exact pack_eval args m env start

private theorem read_cast {context a b : List (Silmaril.Ty Data)} (h : a = b)
    (args : PhiView.Arguments context a) {α : Type w} (env : Env α) :
    PhiView.readArguments (h ▸ args) env = PhiView.readArguments args env := by
  cases h
  rfl

private theorem bound_wires (edge : Edge graph source) :
    packetWires edge = (transfer graph source).outgoing :=
  tabulate_get_eq (transfer graph source).outgoing

section Body
variable (m : Diamond.Model.{u, v, w} Op) (entry : Bank m regs)

private abbrev locals (graph : Graph Op regs n) (source : Fin n) :=
  (transfer graph source).flow.eval m entry PUnit.unit

private theorem transfer_read :
    (transfer graph source).outgoing.read entry (locals m entry graph source) =
      (graph.body source).eval m entry :=
  (compileBlock_read (past := []) (graph.body source) m entry PUnit.unit (initial regs)).trans
    (congrArg (Join.Block.eval (graph.body source) m) (read_initial m entry))

private theorem jump_read {context : List (Silmaril.Ty Data)} (resolve : Resolver graph source context)
    (env : Env (Atom m))
    (matched : ∀ {t} (wire : Origin (dataPorts regs) (bodyPast graph source) t),
      env (resolve wire).val = encodePort m (read m wire entry (locals m entry graph source)))
    (edge : Edge graph source) :
    PhiView.readArguments (jumpArgs (out := out) resolve edge) env =
      encodeTuple m ((graph.body source).eval m entry) := by
  rw [jumpArgs, read_cast, arguments_read m _ _ _ _ matched, bound_wires, transfer_read]

private theorem slot_read {t : Diamond.Ty Data} (port : Port (dataPorts regs) t)
    {env : Env (Atom m)}
    (matched : LayoutMatch m (finalLayout graph source) env entry (locals m entry graph source)) :
    env ((finalLayout graph source).resolve ((transfer graph source).outgoing.get port)).val =
      encodePort m (((graph.body source).eval m entry).get port) := by
  rw [← transfer_read (source := source) m entry, read_get m]
  exact LayoutMatch.resolve m matched ((transfer graph source).outgoing.get port)

private theorem return_read (port : Port (dataPorts regs) (.value out)) {env : Env (Atom m)}
    (matched : LayoutMatch m (finalLayout graph source) env entry (locals m entry graph source)) :
    PhiView.readArguments (returnArgs (finalLayout graph source).resolve port) env =
      .pair (encode m (((graph.body source).eval m entry).get port)) .unit := by
  rw [returnArgs, read_cast]
  change Value.pair (env ((finalLayout graph source).resolve
    ((transfer graph source).outgoing.get port)).val) .unit = _
  rw [slot_read m entry port matched]
  rfl

private theorem tail_observation (term : Terminator graph source out) {env : Env (Atom m)}
    (matched : LayoutMatch m (finalLayout graph source) env entry (locals m entry graph source))
    (start : σ) :
    let resolve : Resolver graph source (finalContext graph source) := (finalLayout graph source).resolve
    let bank := (graph.body source).eval m entry
    let leaf := chosenLeaf resolve m bank term
    let step := term.eval m bank
    leaf.target = stepLabel (m := m) step ∧
      PhiView.readArguments (leafArgs resolve term leaf).val (leafEnv leaf env) =
        stepPayload m bank step ∧
      Semantics.Region.Eval (instruction m) env (terminatorRegion (emit resolve term)) start
        (stepLabel (m := m) step) (stepPayload m bank step) start := by
  cases term with
  | jump edge =>
    have reads := jump_read (out := out) m entry (finalLayout graph source).resolve env
      (fun wire => LayoutMatch.resolve m matched wire) edge
    exact ⟨rfl, reads, .br (pack_eval_of_read _ m env start reads)⟩
  | ret port =>
    have reads := return_read m entry port matched
    exact ⟨rfl, reads, .br (pack_eval_of_read _ m env start reads)⟩
  | branch test onTrue onFalse distinct =>
    have discr := slot_read m entry test matched
    let after := (graph.body source).eval m entry
    let resolve : Resolver graph source (finalContext graph source) := (finalLayout graph source).resolve
    let shifted : Resolver graph source (.unit :: finalContext graph source) := fun {t} (wire : Origin (dataPorts regs) (bodyPast graph source) t) =>
      shiftRef (A := .unit) (resolve wire)
    have shiftMatch : ∀ {t} (wire : Origin (dataPorts regs) (bodyPast graph source) t),
        extend env .unit (shifted wire).val = encodePort m (read m wire entry (locals m entry graph source)) :=
      fun wire => LayoutMatch.resolve m matched wire
    let branch : Terminator graph source out := .branch test onTrue onFalse distinct
    let argument : PhiView.Successor (emit resolve branch) → Value (Atom m) := fun leaf =>
      PhiView.readArguments (leafArgs resolve branch leaf).val (leafEnv leaf env)
    cases taken : (after.get test).down with
    | false =>
      have leaf : chosenLeaf resolve m after branch =
          .right .jump := by
        simp only [branch, chosenLeaf, taken, Bool.false_eq_true, ↓reduceIte]
        rfl
      have reads := jump_read (out := out) m entry shifted (extend env .unit) shiftMatch onFalse
      simp only [Terminator.eval, show (((graph.body source).eval m entry).get test).down =
        false from taken, Bool.false_eq_true, ↓reduceIte, stepLabel, stepPayload]
      refine ⟨congrArg PhiView.Successor.target leaf, (congrArg argument leaf).trans reads, ?_⟩
      refine .case_inr (va := .unit) (s₁ := start) (Semantics.Tm.Eval.var_of_eq ?_)
        (.br (pack_eval_of_read _ m (extend env .unit) start reads))
      simpa [encodePort, encode, after, taken] using discr
    | true =>
      have leaf : chosenLeaf resolve m after branch =
          .left .jump := by
        simp only [branch, chosenLeaf, taken, ↓reduceIte]
        rfl
      have reads := jump_read (out := out) m entry shifted (extend env .unit) shiftMatch onTrue
      simp only [Terminator.eval, show (((graph.body source).eval m entry).get test).down =
        true from taken, ↓reduceIte, stepLabel, stepPayload]
      refine ⟨congrArg PhiView.Successor.target leaf, (congrArg argument leaf).trans reads, ?_⟩
      refine .case_inl (va := .unit) (s₁ := start) (Semantics.Tm.Eval.var_of_eq ?_)
        (.br (pack_eval_of_read _ m (extend env .unit) start reads))
      simpa [encodePort, encode, after, taken] using discr

theorem block_eval (program : Program graph out) (captured : Env (Atom m)) (start : σ) :
    let bank := (graph.body source).eval m entry
    let step := (program.terminator source).eval m bank
    Semantics.Region.Eval (instruction m) (extend captured (encodeTuple m entry))
      (blocks program source) start (stepLabel (m := m) step) (stepPayload m bank step) start := by
  apply unpack_eval m entry captured
  refine schedule_eval m (transfer graph source).flow (layout := startLayout regs) (locals := PUnit.unit)
    ⟨unpackRefs_match m entry captured, trivial⟩ start ?_
  intro env matched
  exact (tail_observation m entry (program.terminator source) matched start).2.2

/-- State-free comparison of the actual occurrence's target and argument. -/
theorem selected_latch (program : Program graph out) {env : Env (Atom m)}
    (matched : LayoutMatch m (finalLayout graph source) env entry ((transfer graph source).flow.eval m entry PUnit.unit)) :
    let bank := (graph.body source).eval m entry
    let occurrence := selectedOccurrence program m bank source
    let step := (program.terminator source).eval m bank
    occurrence.target = stepLabel (m := m) step ∧
      PhiView.latch (phiView program) occurrence (leafEnv occurrence.successor env) =
        stepPayload m bank step := by
  obtain ⟨target, latch, _⟩ := tail_observation m entry (program.terminator source) matched ()
  exact ⟨target, latch⟩

end Body

theorem selected_packet (program : Program graph out) (m : Diamond.Model.{u, v, w} Op)
    (input entry : Bank m regs) (path : Path graph source) (edge : Edge graph source)
    {env : Env (Atom m)}
    (matched : LayoutMatch m (finalLayout graph source) env entry ((transfer graph source).flow.eval m entry PUnit.unit))
    (same : (graph.body source).eval m entry = path.eval m input)
    (taken : (program.terminator source).eval m ((graph.body source).eval m entry) = .inr edge) :
    let occurrence := selectedOccurrence program m ((graph.body source).eval m entry) source
    occurrenceEdge program occurrence = some edge ∧ occurrence.target = edge.target.val ∧
      ∃ bank, headerBank m input edge path = some bank ∧
        PhiView.latch (phiView program) occurrence (leafEnv occurrence.successor env) =
          encodeTuple m bank := by
  have exactEdge := selected_edge program m ((graph.body source).eval m entry) source
  obtain ⟨target, payload⟩ := selected_latch m entry program matched
  rw [taken] at exactEdge
  dsimp only at target payload
  rw [taken] at target payload
  exact ⟨exactEdge, target, path.eval m input, headerBank_agrees edge path m input,
    by simpa [same, stepPayload] using payload⟩

private theorem start_eval (graph : Graph Op regs n) (m : Diamond.Model.{u, v, w} Op)
    (input : Bank m regs) :
    graph.start.2.eval m input = (graph.body graph.start.1).eval m input := by
  induction graph with
  | entry _ => rfl
  | snoc _ _ _ ih =>
    simpa [Graph.start, Graph.body, Path.eval] using ih

section Run
variable (program : Program graph out) (m : Diamond.Model.{u, v, w} Op) (input : Bank m regs)

private theorem follow_runFrom (captured : Env (Atom m)) (start : σ)
    (i : Fin n) (path : Path graph i) (entry : Bank m regs)
    (same : (graph.body i).eval m entry = path.eval m input) :
    Semantics.Region.Follow (instruction m) captured (blocks program) i.val (encodeTuple m entry)
      start 0 (.pair (encode m (program.runFrom m i path (path.eval m input)).result) .unit) start := by
  have step := block_eval (source := i) m entry program captured start
  dsimp only at step
  rw [same] at step
  rw [Program.runFrom]
  cases taken : (program.terminator i).eval m (path.eval m input) with
  | inl result =>
    refine .step (next := n) (middle := .pair (encode m result) .unit) (s₁ := start) i.isLt ?_ ?_
    · simpa [taken, stepLabel, stepPayload] using step
    · simpa using (Semantics.Region.Follow.exit (instr := instruction m) (env := captured)
        (blocks := blocks program) (s := start) (value := .pair (encode m result) .unit) (Nat.le_refl n))
  | inr edge =>
    refine .step (next := edge.target.val) (middle := encodeTuple m (path.eval m input))
      (s₁ := start) i.isLt ?_ ?_
    · simpa [taken, stepLabel, stepPayload] using step
    · dsimp only
      rw [← edge.take_eval path m input]
      exact follow_runFrom captured start edge.target (edge.take path) (path.eval m input)
        (edge.take_eval path m input).symm
termination_by n - i.val
decreasing_by
  have forward := (‹Edge graph i›).forward
  omega

private theorem entry_read :
    PhiView.readArguments (entryArgs regs) (inputEnv m input) = encodeTuple m input := by
  have matched : LayoutMatch m (Layout.initial (dataPorts regs)) (inputEnv m input)
      input PUnit.unit :=
    ⟨Diamond.LambdaSSA.inputRefs_match m input, trivial⟩
  exact (arguments_read m _ _ _ _ (fun wire => LayoutMatch.resolve m matched wire)
    (initial regs)).trans (congrArg (encodeTuple m) (read_initial m input))

theorem lower_eval (start : σ) :
    Semantics.Region.Eval (instruction m) (inputEnv m input) (lower program) start
      0 (.pair (encode m (program.run m input).result) .unit) start := by
  refine .cfg (initial := encodeTuple m input) (s₁ := start)
    (.br (pack_eval_of_read (entryArgs regs) m (inputEnv m input) start (entry_read m input))) ?_
  simpa only [Program.run, start_eval] using follow_runFrom program m input (inputEnv m input)
    start graph.start.1 graph.start.2 input (start_eval graph m input).symm

theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m input) (lower program) start label payload finish ↔
      label = 0 ∧ payload = .pair (encode m (program.run m input).result) .unit ∧ finish = start := by
  constructor
  · intro observed
    exact observed.deterministic (instruction_deterministic m) (lower_eval program m input start)
  · rintro ⟨labelEq, payloadEq, stateEq⟩
    subst label
    subst payload
    subst finish
    exact lower_eval program m input start

theorem returns_iff (start : σ) (result : sortValue m.value out) :
    Semantics.Region.Eval (instruction m) (inputEnv m input) (lower program) start 0
        (.pair (encode m result) .unit) start ↔
      (program.run m input).result = result := by
  rw [lower_eval_iff program m input]
  constructor
  · rintro ⟨_, payload, _⟩
    exact Diamond.LambdaSSA.encode_injective m (Value.pair.inj payload).1.symm
  · intro returned
    simp [returned]

end Run

end Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA.Proofs

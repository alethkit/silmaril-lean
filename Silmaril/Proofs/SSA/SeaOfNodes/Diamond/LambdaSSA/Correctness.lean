module

public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Thms
public import Silmaril.SSA.PhiView.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA

open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Diamond
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env InstrDeterministic)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data} {σ : Type x}
variable {args : List (Diamond.Ty Data)} {past sigs : List (List (Diamond.Ty Data))}
variable {context : List (Code Data)}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}
variable (m : Model.{u,v,w} Op)

theorem encode_injective {sort : ValueSort Data} :
    Function.Injective (encode m (sort := sort)) := by
  cases sort with
  | predicate =>
    intro ⟨a⟩ ⟨b⟩ h
    cases a <;> cases b <;> first | rfl | cases h
  | data d =>
    intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Value.atom.inj h)).2

theorem encodeTuple_injective (ins : List (ValueSort Data)) :
    Function.Injective (encodeTuple m (ports := dataPorts ins)) := by
  induction ins with
  | nil => intro a b _; cases a; cases b; rfl
  | cons sort rest ih =>
    intro a b same
    cases a with
    | cons a as =>
      cases b with
      | cons b bs =>
        obtain ⟨head, tail⟩ := Value.pair.inj same
        obtain rfl := encode_injective m (sort := sort) head
        obtain rfl := ih tail
        rfl

theorem instruction_deterministic : InstrDeterministic (instruction m (σ := σ)) := by
  intro opcode input start result finish result' finish' eval eval'
  cases opcode with
  | apply op =>
    obtain ⟨a, encoded, rfl, rfl⟩ := eval
    obtain ⟨b, encoded', rfl, rfl⟩ := eval'
    obtain rfl := encodeTuple_injective m _ (encoded.symm.trans encoded')
    exact ⟨rfl, rfl⟩

private theorem wireTerm_typed (layout : Layout args past context)
    {ports : List (Diamond.Ty Data)} (wires : Wires args past ports) :
    (wireTerm layout wires : Tm (Primitive Op)).HasType context
      (PhiView.packedType (ports.map portCode)) := by
  induction wires with
  | nil => exact .unit
  | cons origin _ ih => exact .pair (.var (layout.resolve origin).property) ih

theorem schedule_typed (flow : Dataflow Op args past sigs)
    (layout : Layout args past context) {tail : Region (Primitive Op)} {labels : List (Code Data)}
    (typed : tail.HasType (scheduledContext context sigs) labels) :
    (schedule flow layout tail).HasType context labels := by
  induction flow generalizing context with
  | nil => exact typed
  | cons op wires rest ih => exact .let₁ (.op (wireTerm_typed layout wires)) (ih _ typed)

private theorem terminatorRegion_typed {term : Terminator (Primitive Op)}
    {labels : List (Code Data)} (typed : term.HasType context labels) :
    (terminatorRegion term).HasType context labels := by
  induction typed with
  | br label arg => exact .br label arg
  | case discr _ _ left right => exact .case discr left right

variable (g : Graph Op inputs sigs out)

private abbrev joinCode (out : ValueSort Data) := PhiView.packedType [sortCode out]

theorem lower_hasType :
    (lower g).HasType (initialContext inputs) [sortCode out] := by
  refine .cfg (fun _ => joinCode out) (schedule_typed _ _ (terminatorRegion_typed ?_)) ?_
  · exact .case (.var ((finalLayout g).resolve g.predicate).property)
      (PhiView.branch_hasType (phiView g).table (projectionEdge g .onTrue) rfl)
      (PhiView.branch_hasType (phiView g).table (projectionEdge g .onFalse) rfl)
  · intro _
    exact .let₂ (.var (i := 0) rfl) (.br (ℓ := 1) rfl (.var (i := 1) rfl))

theorem edge_branch (slot : Slot) :
    (phiView g).table.branch (edge g slot) = .br 0 (PhiView.packTerm (slotArguments g slot)) := by
  have emitted (projection : Projection) :
      (phiView g).table.branch (projectionEdge g projection) =
        .br 0 (PhiView.packTerm (slotArguments g (g.phi.merge.slot projection))) := by
    rw [PhiView.branch_eq (phiView g)]
    cases projection <;> rfl
  rw [edge, emitted, Merge.slot_predecessor]

private theorem projection_latch (projection : Projection) (old : Env (Atom m)) :
    PhiView.latch (phiView g) (projectionEdge g projection) (Semantics.extend old .unit) =
      .pair (old ((finalLayout g).resolve (g.phi.operand (g.phi.merge.slot projection))).val) .unit := by
  cases projection <;> rfl

theorem edge_latch (slot : Slot) (old : Env (Atom m)) :
    PhiView.latch (phiView g) (edge g slot) (Semantics.extend old .unit) =
      .pair (old ((finalLayout g).resolve (g.phi.operand slot)).val) .unit := by
  rw [edge, projection_latch, Merge.slot_predecessor]

theorem edge_transfer_iff (slot : Slot) (old : Env (Atom m)) (start finish : σ)
    (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (Semantics.extend old .unit)
        (.br (edge g slot).target (edge g slot).argument) start label payload finish ↔
      label = 0 ∧ payload = .pair (old ((finalLayout g).resolve (g.phi.operand slot)).val) .unit ∧
        finish = start := by
  have target : (edge g slot).target = 0 := by
    unfold edge
    cases g.phi.merge.predecessor slot <;> rfl
  rw [PhiView.latch_eq_transfer (instruction m) (phiView g), edge_latch, target]

theorem get_map {T : Type u} {F : T → Type v} {G : T → Type w}
    {ports : List T} {t : T} (f : ∀ t, F t → G t) (xs : Tuple F ports) (p : Port ports t) :
    (xs.map f).get p = f t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs with | cons _ rest => exact ih rest

private theorem tupleMatch_shift {ports : List (Diamond.Ty Data)} {A : Code Data}
    {env : Env (Atom m)} {refs : Tuple (Ref context) ports} {values : Tuple (Val m.value) ports}
    (ok : TupleMatch m env refs values) (value : Value (Atom m)) :
    TupleMatch m (context := A :: context)
      (Semantics.extend env value) (refs.map fun _ => shiftRef) values := by
  intro _ slot
  rw [get_map]
  exact ok slot

theorem inputRefs_match {ports : List (Diamond.Ty Data)} (values : Tuple (Val m.value) ports) :
    TupleMatch m (inputEnv m values) (inputRefs ports) values := by
  induction values with
  | nil => intro _ slot; cases slot
  | cons v rest ih =>
    intro _ slot
    cases slot with
    | head => rfl
    | tail slot => exact tupleMatch_shift m ih (encodePort m v) slot

private theorem localsMatch_get {env : Env (Atom m)}
    {refs : Locals (Ref context) past} {locals : Locals (Val m.value) past}
    (matched : LocalsMatch m env refs locals) (i : Fin past.length) :
    TupleMatch m env (refs.get i) (locals.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons _ _ ih =>
    exact Fin.cases (motive := fun j => TupleMatch m env (refs.get j) (locals.get j))
      matched.1 (fun j => ih matched.2 j) i

private theorem localsMatch_push {env : Env (Atom m)}
    {refs : Locals (Ref context) past} {locals : Locals (Val m.value) past}
    (matched : LocalsMatch m env refs locals) (result : sortValue m.value out) :
    LocalsMatch m (Semantics.extend env (encode m result)) (pushLocalRefs out refs)
      (locals.snoc (.cons result .nil)) := by
  induction past with
  | nil =>
    refine ⟨?_, trivial⟩
    intro _ slot
    cases slot with
    | head => rfl
    | tail impossible => cases impossible
  | cons _ _ ih => exact ⟨tupleMatch_shift m matched.1 _, ih matched.2⟩

theorem LayoutMatch.resolve {layout : Layout args past context}
    {env : Env (Atom m)} {entry : Tuple (Val m.value) args} {locals : Locals (Val m.value) past}
    (matched : LayoutMatch m layout env entry locals) {port : Diamond.Ty Data}
    (origin : Origin args past port) :
    env (layout.resolve origin).val = encodePort m (read m origin entry locals) := by
  cases origin with
  | arg p => exact matched.1 p
  | output i p => exact localsMatch_get m matched.2 i p

private theorem LayoutMatch.push {layout : Layout args past context}
    {env : Env (Atom m)} {entry : Tuple (Val m.value) args} {locals : Locals (Val m.value) past}
    (matched : LayoutMatch m layout env entry locals) (result : sortValue m.value out) :
    LayoutMatch m (layout.push out) (Semantics.extend env (encode m result)) entry
      (locals.snoc (.cons result .nil)) :=
  ⟨tupleMatch_shift m matched.1 _, localsMatch_push m matched.2 result⟩

private theorem wireTerm_eval {layout : Layout args past context}
    {env : Env (Atom m)} {entry : Tuple (Val m.value) args} {locals : Locals (Val m.value) past}
    (matched : LayoutMatch m layout env entry locals) {ports : List (Diamond.Ty Data)}
    (wires : Wires args past ports) (start : σ) :
    Semantics.Tm.Eval (instruction m) env (wireTerm layout wires) start
      (encodeTuple m (wires.read entry locals)) start := by
  induction wires with
  | nil => exact .unit
  | cons origin rest ih =>
    exact .pair (Semantics.Tm.Eval.var_of_eq (LayoutMatch.resolve m matched origin)) ih

theorem schedule_eval (flow : Dataflow Op args past sigs)
    {layout : Layout args past context} {env : Env (Atom m)}
    {entry : Tuple (Val m.value) args} {locals : Locals (Val m.value) past}
    (matched : LayoutMatch m layout env entry locals) {tail : Region (Primitive Op)}
    {label : Nat} {payload : Value (Atom m)} (start : σ)
    (runTail : ∀ finalEnv, LayoutMatch m (scheduleLayout flow layout) finalEnv entry
        (flow.eval m entry locals) →
      Semantics.Region.Eval (instruction m) finalEnv tail start label payload start) :
    Semantics.Region.Eval (instruction m) env (schedule flow layout tail) start label payload start := by
  induction flow generalizing context env with
  | nil => exact runTail env matched
  | cons op wires rest ih =>
    refine .let₁ (.op (wireTerm_eval m matched wires start) ⟨wires.read entry locals, rfl, rfl, rfl⟩) ?_
    exact ih (LayoutMatch.push m matched (m.run op (wires.read entry locals))) runTail

private theorem dispatch_eval {env : Env (Atom m)} {entry : Tuple (Val m.value) (dataPorts inputs)}
    (matched : LayoutMatch m (finalLayout g) env entry (g.dataflow.eval m entry PUnit.unit))
    (start : σ) :
    Semantics.Region.Eval (instruction m) env (terminatorRegion (dispatch g)) start
      0 (.pair (encode m (g.denote m entry)) .unit) start := by
  generalize dataResult : g.dataflow.eval m entry PUnit.unit = locals at matched
  have discr := LayoutMatch.resolve m matched g.predicate
  cases selected : (read m g.predicate entry locals).down with
  | false =>
    refine .case_inr (va := .unit) (Semantics.Tm.Eval.var_of_eq ?_) ?_
    · simpa [encodePort, encode, selected] using discr
    · apply (PhiView.latch_eq_transfer (instruction m) (phiView g)
        (projectionEdge g .onFalse) _ _ _ _ _).mpr
      refine ⟨rfl, ?_, rfl⟩
      rw [projection_latch, LayoutMatch.resolve m matched (g.phi.operand (g.phi.merge.slot .onFalse))]
      simp only [Graph.denote, dataResult, selected, Projection.ofBool, encodePort]
  | true =>
    refine .case_inl (va := .unit) (Semantics.Tm.Eval.var_of_eq ?_) ?_
    · simpa [encodePort, encode, selected] using discr
    · apply (PhiView.latch_eq_transfer (instruction m) (phiView g)
        (projectionEdge g .onTrue) _ _ _ _ _).mpr
      refine ⟨rfl, ?_, rfl⟩
      rw [projection_latch, LayoutMatch.resolve m matched (g.phi.operand (g.phi.merge.slot .onTrue))]
      simp only [Graph.denote, dataResult, selected, Projection.ofBool, encodePort]

private theorem lower_eval_denote (entry : Tuple (Val m.value) (dataPorts inputs)) (start : σ) :
    Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start
      0 (encode m (g.denote m entry)) start := by
  refine .cfg (schedule_eval m g.dataflow ⟨inputRefs_match m entry, trivial⟩ start
    (fun _ matched => dispatch_eval m g matched start)) ?_
  exact .step (by decide) (.let₂ .var (.br .var)) (.exit (by decide))

theorem lower_eval_iff (entry : Tuple (Val m.value) (dataPorts inputs))
    (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start label payload finish ↔
      label = 0 ∧ payload = encode m (g.denote m entry) ∧ finish = start := by
  constructor
  · intro eval
    exact eval.deterministic (instruction_deterministic m) (lower_eval_denote m g entry start)
  · rintro ⟨rfl, rfl, same⟩
    subst finish
    exact lower_eval_denote m g entry start

theorem returns_iff (entry : Tuple (Val m.value) (dataPorts inputs)) (start : σ)
    (result : sortValue m.value out) :
    g.Returns m entry result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start 0 (encode m result) start := by
  rw [g.returns_iff_denote, lower_eval_iff]
  exact ⟨fun h => ⟨rfl, congrArg (encode m) h.symm, rfl⟩,
    fun h => (encode_injective m h.2.1).symm⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.LambdaSSA

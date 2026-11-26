module

public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
public import Silmaril.SSA.PhiView.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic

open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes
open Loop Loop.LambdaSSA.Generic
open Diamond (Model Val ValueSort dataPorts read sortValue)
open Diamond.LambdaSSA
open Silmaril.SSA.RVSDG (Origin Port Tuple Wires)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data} {σ : Type x}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}
variable {context : List (Code Data)} {ports : List (Diamond.Ty Data)}
variable (m : Model.{u,v,w} Op)

theorem unpack_typed (ports : List (Diamond.Ty Data)) {context : List (Code Data)}
    {tail : Region (Primitive Op)} {labels : List (Code Data)}
    (typed : tail.HasType (unpackContext context ports) labels) :
    (unpack ports tail).HasType (packed ports :: context) labels := by
  induction ports generalizing context with
  | nil => exact typed
  | cons port rest ih =>
    exact .let₂ (A := portCode port) (B := packed rest) (.var (i := 0) rfl) (ih typed)

theorem unpack_eval (values : Tuple (Val m.value) ports) (captured : Env (Atom m))
    {tail : Region (Primitive Op)} {start finish : σ} {label : Nat} {payload : Value (Atom m)}
    (runTail : Semantics.Region.Eval (instruction m) (unpackEnv m values captured)
      tail start label payload finish) :
    Semantics.Region.Eval (instruction m) (extend captured (encodeTuple m values))
      (unpack ports tail) start label payload finish := by
  induction values generalizing captured with
  | nil => exact runTail
  | cons x rest ih => exact .let₂ .var (ih _ runTail)

private theorem weakenUnpack_read (values : Tuple (Val m.value) ports) (captured : Env (Atom m))
    {port : Diamond.Ty Data} (ref : Ref (packed ports :: context) port) :
    unpackEnv m values captured (weakenUnpack ports ref).val =
      extend captured (encodeTuple m values) ref.val := by
  induction values generalizing captured context with
  | nil => rfl
  | cons x rest ih => exact ih _ (shiftRef (shiftRef ref))

private theorem unpackRefs_match (values : Tuple (Val m.value) ports) (captured : Env (Atom m)) :
    TupleMatch m (unpackEnv m values captured) (unpackRefs ports (context := context)) values := by
  induction values generalizing captured context with
  | nil => intro _ p; cases p
  | cons x rest ih =>
    intro _ p
    cases p with
    | head => exact weakenUnpack_read m rest _ ⟨1, rfl⟩
    | tail p => exact ih _ p

private theorem append_match {ls rs : List (Diamond.Ty Data)} {env : Env (Atom m)}
    {leftRefs : Tuple (Ref context) ls} {rightRefs : Tuple (Ref context) rs}
    {left : Tuple (Val m.value) ls} {right : Tuple (Val m.value) rs}
    (leftMatch : TupleMatch m env leftRefs left) (rightMatch : TupleMatch m env rightRefs right) :
    TupleMatch m env (appendTuple rightRefs leftRefs) (appendTuple right left) := by
  induction left with
  | nil => cases leftRefs; exact rightMatch
  | cons x rest ih =>
    cases leftRefs with
    | cons ref refs =>
      intro _ p
      cases p with
      | head => exact leftMatch .head
      | tail p => exact ih (fun q => leftMatch (.tail q)) p

private theorem headerStart_match (input : Tuple (Val m.value) (dataPorts inputs))
    (old : Tuple (Val m.value) (dataPorts carried)) :
    LayoutMatch m (headerStart inputs carried) (unpackEnv m old (inputEnv m input))
      (appendTuple old input) PUnit.unit := by
  refine ⟨append_match m ?_ (unpackRefs_match m old _), trivial⟩
  intro _ p
  rw [tuple_get_map]
  exact (weakenUnpack_read m old _ _).trans (inputRefs_match m input p)

private theorem arguments_read {args : List (Diamond.Ty Data)} {past : List (List (Diamond.Ty Data))}
    (resolve : ∀ {p}, Origin args past p → Ref context p)
    (env : Env (Atom m)) (entry : Tuple (Val m.value) args) (locals : RVSDG.Locals (Val m.value) past)
    (matched : ∀ {p} (wire : Origin args past p), env (resolve wire).val = encodePort m (read m wire entry locals))
    (wires : Wires args past ports) :
    PhiView.readArguments (arguments resolve wires) env = encodeTuple m (wires.read entry locals) := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    change Value.pair (env (resolve wire).val) (PhiView.readArguments (arguments resolve rest) env) =
      Value.pair (encodePort m (read m wire entry locals)) (encodeTuple m (Wires.read rest entry locals))
    rw [matched wire, ih]

variable (g : Graph Op inputs carried entrySigs headerSigs out)

theorem lower_hasType : (lower g).HasType ((dataPorts inputs).map portCode) [packed [.value out]] := by
  refine .cfg (fun _ => packed (dataPorts carried)) ?_ (fun _ => ?_)
  · apply schedule_typed
    exact .br (ℓ := 0) rfl (PhiView.packTerm_hasType (entryArgs g))
  · apply unpack_typed
    apply schedule_typed
    exact .case (A := .unit) (B := .unit) (.var ((headerLayout g).resolve g.predicate).property)
      (.br (ℓ := 0) rfl (PhiView.packTerm_hasType (feedbackArgs g)))
      (.br (ℓ := 1) rfl (PhiView.packTerm_hasType (exitArgs g)))

variable (input : Tuple (Val m.value) (dataPorts inputs))
variable (old : Tuple (Val m.value) (dataPorts carried))

theorem entry_latch {env : Env (Atom m)}
    (matched : LayoutMatch m (entryLayout g) env input (g.preheader.eval m input PUnit.unit)) :
    PhiView.latch (phiView g) (edge g .entry) env = encodeTuple m (g.initial m input) :=
  arguments_read m _ env _ _ (fun wire => LayoutMatch.resolve m matched wire) (g.phiInputs .entry)

theorem feedback_latch {env : Env (Atom m)}
    (matched : LayoutMatch m (headerLayout g) env (appendTuple old input)
      (g.header.eval m (appendTuple old input) PUnit.unit)) :
    PhiView.latch (phiView g) (edge g .backedge) (extend env .unit) =
      encodeTuple m (g.latch m .backedge (appendTuple old input)
        (g.header.eval m (appendTuple old input) PUnit.unit)) :=
  arguments_read m (fun wire => shiftRef (A := .unit) ((headerLayout g).resolve wire))
    (extend env .unit) _ _ (fun wire => LayoutMatch.resolve m matched wire)
    (g.phiInputs .backedge)

theorem entry_eval (start : σ) :
    Semantics.Region.Eval (instruction m) (inputEnv m input) (entry g) start
      0 (encodeTuple m (g.initial m input)) start := by
  refine schedule_eval m g.preheader (locals := PUnit.unit) ⟨inputRefs_match m input, trivial⟩ start ?_
  intro env matched
  apply (PhiView.latch_eq_transfer (instruction m) (phiView g) (edge g .entry) _ _ _ _ _).mpr
  exact ⟨rfl, (entry_latch m g input matched).symm, rfl⟩

theorem body_eval (start : σ) :
    Semantics.Region.Eval (instruction m) (unpackEnv m old (inputEnv m input)) (body g) start
      (stepLabel m (g.step m input old)) (stepPayload m (g.step m input old)) start := by
  refine schedule_eval m g.header (headerStart_match m input old) start ?_
  intro env matched
  change LayoutMatch m (headerLayout g) env (appendTuple old input)
    (g.header.eval m (appendTuple old input) PUnit.unit) at matched
  have predicate := LayoutMatch.resolve m matched g.predicate
  have result := LayoutMatch.resolve m matched g.result
  let args := appendTuple old input
  let locals := g.header.eval m args PUnit.unit
  change Semantics.Region.Eval (instruction m) env (terminatorRegion (terminators g .header)) start
    (stepLabel m (if (read m g.predicate args locals).down then .inr (g.latch m .backedge args locals)
      else .inl (read m g.result args locals)))
    (stepPayload m (if (read m g.predicate args locals).down then .inr (g.latch m .backedge args locals)
      else .inl (read m g.result args locals))) start
  cases taken : (read m g.predicate args locals).down with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, stepLabel, stepPayload]
    refine .case_inr (va := .unit) (Semantics.Tm.Eval.var_of_eq ?_) ?_
    · simpa [encodePort, encode, args, locals, taken] using predicate
    · exact .br (.pair (Semantics.Tm.Eval.var_of_eq result) .unit)
  | true =>
    simp only [↓reduceIte, stepLabel, stepPayload]
    refine .case_inl (va := .unit) (Semantics.Tm.Eval.var_of_eq ?_) ?_
    · simpa [encodePort, encode, args, locals, taken] using predicate
    · apply (PhiView.latch_eq_transfer (instruction m) (phiView g) (edge g .backedge) _ _ _ _ _).mpr
      exact ⟨rfl, (feedback_latch m g input old matched).symm, rfl⟩

theorem header_eval (start : σ) :
    Semantics.Region.Eval (instruction m) (extend (inputEnv m input) (encodeTuple m old))
      (header g) start (stepLabel m (g.step m input old)) (stepPayload m (g.step m input old)) start :=
  unpack_eval m old (inputEnv m input) (body_eval m g input old start)

end Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic

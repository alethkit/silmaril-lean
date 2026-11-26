module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Thms
public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
public import Silmaril.SSA.PhiView.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA

open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes
open SeaOfNodes.Diamond SeaOfNodes.Diamond.Arms
open SeaOfNodes.Diamond.LambdaSSA SeaOfNodes.Diamond.Arms.LambdaSSA
open RVSDG (Locals Tuple Wires extend)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data} {σ : Type x}
variable {args : List (Diamond.Ty Data)} {past : List (List (Diamond.Ty Data))}
variable {context : List (Code Data)}
variable {inputs results : List (ValueSort Data)} {sigs : List (List (Diamond.Ty Data))}
variable (m : Model.{u,v,w} Op)

private theorem shift_tuple_match {ports : List (Diamond.Ty Data)} {A : Code Data}
    {env : Env (Atom m)} {refs : Tuple (Ref context) ports} {values : Tuple (Val m.value) ports}
    (matched : TupleMatch m env refs values) (arg : Value (Atom m)) :
    TupleMatch m (context := A :: context) (Semantics.extend env arg)
      (refs.map (fun _ => shiftRef)) values := by
  intro _ port
  rw [tuple_get_map]
  exact matched port

private theorem shift_locals_match {A : Code Data} {env : Env (Atom m)}
    {refs : Locals (Ref context) past} {values : Locals (Val m.value) past}
    (matched : LocalsMatch m env refs values) (arg : Value (Atom m)) :
    LocalsMatch m (Semantics.extend env arg) (shiftLocals A refs) values := by
  induction past with
  | nil => trivial
  | cons _ _ ih => exact ⟨shift_tuple_match m matched.1 arg, ih matched.2⟩

private theorem armStart_match {layout : Layout args past context} {env : Env (Atom m)}
    {entry : Tuple (Val m.value) args} {locals : Locals (Val m.value) past}
    (matched : LayoutMatch m layout env entry locals) :
    LayoutMatch m (armStart layout) (Semantics.extend env .unit) entry locals :=
  ⟨shift_tuple_match m matched.1 _, shift_locals_match m matched.2 _⟩

private theorem arguments_read {layout : Layout args past context} {env : Env (Atom m)}
    {entry : Tuple (Val m.value) args} {locals : Locals (Val m.value) past}
    (matched : LayoutMatch m layout env entry locals) {ports : List (Diamond.Ty Data)}
    (wires : Wires args past ports) :
    PhiView.readArguments (SeaOfNodes.Loop.LambdaSSA.Generic.arguments layout.resolve wires) env =
      encodeTuple m (wires.read entry locals) := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    change Value.pair (env (layout.resolve wire).val)
      (PhiView.readArguments (SeaOfNodes.Loop.LambdaSSA.Generic.arguments layout.resolve rest) env) =
      Value.pair (encodePort m (read m wire entry locals)) (encodeTuple m (Wires.read rest entry locals))
    rw [LayoutMatch.resolve m matched, ih]

private theorem encode_results_injective (results : List (ValueSort Data)) :
    Function.Injective (encodeTuple m (ports := dataPorts results)) := by
  induction results with
  | nil => intro a b _; cases a; cases b; rfl
  | cons sort sorts ih =>
    intro a b equal
    cases a with
    | cons a as =>
      cases b with
      | cons b bs =>
        obtain ⟨head, tail⟩ := Value.pair.inj equal
        obtain rfl := encode_injective m (sort := sort) head
        obtain rfl := ih tail
        rfl

variable (g : Arms.Graph Op inputs sigs results)

private abbrev labels := ([.unit, .unit, resultCode results, resultCode results] : List (Code Data))

private theorem armBlock_typed (p : Projection) :
    (armBlock g p).HasType (.unit :: finalContext inputs sigs) (labels (results := results)) := by
  apply schedule_typed
  have typed := PhiView.branch_hasType (phiView g).table (incoming g p)
    (labels := labels (results := results)) rfl
  rw [PhiView.branch_eq (phiView g)] at typed
  cases typed with
  | br target arg => exact .br target arg

theorem lower_hasType : (lower g).HasType (initialContext inputs) [resultCode results] := by
  apply schedule_typed
  refine .cfg (blockTypes results) ?_ ?_
  · exact .case (A := .unit) (B := .unit) (.var ((sharedLayout g).resolve g.predicate).property)
      (.br (ℓ := 0) rfl .unit) (.br (ℓ := 1) rfl .unit)
  · refine Fin.cases (armBlock_typed g .onTrue) (Fin.cases (armBlock_typed g .onFalse) ?_)
    intro _
    exact .br (ℓ := 3) rfl (.var (i := 0) rfl)

variable {g}
variable (entry : Tuple (Val m.value) (dataPorts inputs))

theorem incoming_latch (p : Projection) {env : Env (Atom m)}
    (matched : LayoutMatch m (armLayout g p) env entry
      ((selectedArm g p).dataflow.eval m entry (g.shared.eval m entry PUnit.unit))) :
    PhiView.latch (phiView g) (incoming g p) env =
      encodeTuple m ((selectedArm g p).eval m entry (g.shared.eval m entry PUnit.unit)) :=
  arguments_read m matched (selectedArm g p).outputs

theorem edge_latch (slot : Slot) {env : Env (Atom m)}
    (matched : LayoutMatch m (armLayout g (g.merge.predecessor slot)) env entry
      ((selectedArm g (g.merge.predecessor slot)).dataflow.eval m entry
        (g.shared.eval m entry PUnit.unit))) :
    PhiView.latch (phiView g) (edge g slot) env =
      encodeTuple m ((g.arms slot).eval m entry (g.shared.eval m entry PUnit.unit)) := by
  calc
    _ = encodeTuple m ((selectedArm g (g.merge.predecessor slot)).eval m entry
          (g.shared.eval m entry PUnit.unit)) := incoming_latch m entry _ matched
    _ = _ := by rw [selectedArm, Merge.slot_predecessor]

theorem arm_eval (p : Projection) {env : Env (Atom m)}
    (matched : LayoutMatch m (sharedLayout g) env entry (g.shared.eval m entry PUnit.unit))
    (start : σ) :
    Semantics.Region.Eval (instruction m) (Semantics.extend env .unit) (armBlock g p) start
      2 (encodeTuple m ((selectedArm g p).eval m entry (g.shared.eval m entry PUnit.unit))) start := by
  refine schedule_eval m (selectedArm g p).dataflow (armStart_match m matched) start ?_
  intro finalEnv finalMatch
  apply (PhiView.latch_eq_transfer (instruction m) (phiView g) (incoming g p) _ _ _ _ _).mpr
  exact ⟨rfl, (incoming_latch m entry p finalMatch).symm, rfl⟩

private theorem cfg_eval {env : Env (Atom m)}
    (matched : LayoutMatch m (sharedLayout g) env entry (g.shared.eval m entry PUnit.unit))
    (start : σ) :
    Semantics.Region.Eval (instruction m) env (.cfg (dispatch g) 3 (blocks g)) start
      0 (encodeTuple m (g.denote m entry)) start := by
  have discr := LayoutMatch.resolve m matched g.predicate
  have join (result : Value (Atom m)) :
      Semantics.Region.Follow (instruction m) env (blocks g) 2 result start 0 result start :=
    .step (by decide) (.br .var) (.exit (by decide))
  dsimp only [Arms.Graph.denote]
  cases selected : (read m g.predicate entry (g.shared.eval m entry PUnit.unit)).down with
  | false =>
    refine .cfg (.case_inr (va := .unit) (Semantics.Tm.Eval.var_of_eq ?_) (.br .unit)) ?_
    · simpa [encodePort, encode, selected] using discr
    · refine .step (by decide) ?_ (join _)
      exact arm_eval m entry .onFalse matched start
  | true =>
    refine .cfg (.case_inl (va := .unit) (Semantics.Tm.Eval.var_of_eq ?_) (.br .unit)) ?_
    · simpa [encodePort, encode, selected] using discr
    · refine .step (by decide) ?_ (join _)
      exact arm_eval m entry .onTrue matched start

private theorem lower_eval_denote (start : σ) :
    Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start
      0 (encodeTuple m (g.denote m entry)) start :=
  schedule_eval m g.shared (locals := PUnit.unit) ⟨inputRefs_match m entry, trivial⟩ start
    (fun _ matched => cfg_eval m entry matched start)

theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start label payload finish ↔
      label = 0 ∧ payload = encodeTuple m (g.denote m entry) ∧ finish = start := by
  constructor
  · intro run
    exact run.deterministic (instruction_deterministic m) (lower_eval_denote m entry start)
  · rintro ⟨rfl, rfl, same⟩
    subst finish
    exact lower_eval_denote m entry start

theorem returns_iff (start : σ) (result : Tuple (Val m.value) (dataPorts results)) :
    g.Returns m entry result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m entry) (lower g) start
        0 (encodeTuple m result) start := by
  rw [g.returns_iff_denote, lower_eval_iff m entry]
  exact ⟨fun eq => ⟨rfl, congrArg (encodeTuple m) eq.symm, rfl⟩,
    fun eval => (encode_results_injective m results eval.2.1).symm⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA

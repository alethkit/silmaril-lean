module

public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.SSA.PhiView.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Correctness
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Activation

/-! # Typing and finite operational agreement of the generated CFG -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic

open Diamond (Model Val ValueSort dataPorts read sortValue)
open Diamond.LambdaSSA (Atom Code LayoutMatch Primitive Ref TupleMatch encodePort encodeTuple inputEnv instruction)
open RVSDG (Locals Origin Tuple Wires)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data} {σ : Type x}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}
variable (g : Graph Op inputs carried entrySigs headerSigs out)

section Unpack

variable {ports : List (Diamond.Ty Data)} {context labels : List (Code Data)}
variable {tail : Region (Primitive Op)}

/-- A region following tuple destructuring sees the expanded variable context. -/
theorem unpack_typed (ports : List (Diamond.Ty Data))
    (typed : tail.HasType (unpackContext context ports) labels) :
    (unpack ports tail).HasType (packed ports :: context) labels :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.unpack_typed ports typed

/-- Structurally decode a packed tuple, preserving the observation of the tail. -/
theorem unpack_eval (m : Model.{u,v,w} Op) (values : Tuple (Val m.value) ports) (captured : Env (Atom m))
    {start finish : σ} {label : Nat} {payload : Value (Atom m)}
    (runTail : Semantics.Region.Eval (instruction m) (unpackEnv m values captured)
      tail start label payload finish) :
    Semantics.Region.Eval (instruction m) (extend captured (encodeTuple m values))
      (unpack ports tail) start label payload finish :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.unpack_eval m values captured runTail

/-- The unpacked references denote the supplied fields of the block parameter. -/
theorem unpackRefs_match (m : Model.{u,v,w} Op) (values : Tuple (Val m.value) ports)
    (captured : Env (Atom m)) :
    TupleMatch m (unpackEnv m values captured) (unpackRefs ports (context := context)) values :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.unpackRefs_match m values captured

/-- Resolving a typed wire vector as a branch argument reads that vector in order. -/
theorem arguments_read {args : List (Diamond.Ty Data)} {past : List (List (Diamond.Ty Data))}
    (m : Model.{u,v,w} Op) (resolve : ∀ {p}, Origin args past p → Ref context p)
    (env : Env (Atom m)) (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (matched : ∀ {p} (wire : Origin args past p), env (resolve wire).val = encodePort m (read m wire entry locals))
    (wires : Wires args past ports) :
    PhiView.readArguments (arguments resolve wires) env = encodeTuple m (wires.read entry locals) :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.arguments_read m resolve env entry locals matched wires

end Unpack

theorem lower_hasType : (lower g).HasType (inputContext inputs) [packed [.value out]] :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.lower_hasType g

theorem incoming_distinct : edge g .entry ≠ edge g .backedge := fun same => by cases same

theorem edge_branch (arrival : Incoming) :
    (phiView g).table.branch (edge g arrival) = .br 0 (edge g arrival).argument := by
  rw [PhiView.branch_eq (phiView g)]
  cases arrival <;> rfl

variable (m : Model.{u,v,w} Op)
variable (input : Tuple (Val m.value) (dataPorts inputs))

theorem entry_latch {env : Env (Atom m)}
    (matched : LayoutMatch m (entryLayout g) env input (g.preheader.eval m input PUnit.unit)) :
    PhiView.latch (phiView g) (edge g .entry) env = encodeTuple m (g.initial m input) :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.entry_latch m g input matched

theorem entry_eval (start : σ) :
    Semantics.Region.Eval (instruction m) (inputEnv m input) (entry g) start
      0 (encodeTuple m (g.initial m input)) start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.entry_eval m g input start

variable (old : Tuple (Val m.value) (dataPorts carried))

/-- Every next-carried wire reads from the same old activation, including
references to a previous carried value or to this activation's producers. -/
theorem feedback_latch {env : Env (Atom m)}
    (matched : LayoutMatch m (headerLayout g) env (appendTuple old input)
      (g.header.eval m (appendTuple old input) PUnit.unit)) :
    PhiView.latch (phiView g) (edge g .backedge) (extend env .unit) =
      encodeTuple m (g.latch m .backedge (appendTuple old input)
        (g.header.eval m (appendTuple old input) PUnit.unit)) :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.feedback_latch m g input old matched

/-- Execute the emitted producer lets and the ordinary λSSA case on the
compiled predicate variable. The source step determines the observation. -/
theorem body_eval (start : σ) :
    Semantics.Region.Eval (instruction m) (unpackEnv m old (inputEnv m input)) (body g) start
      (stepLabel m (g.step m input old)) (stepPayload m (g.step m input old)) start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.body_eval m g input old start

theorem header_eval (start : σ) :
    Semantics.Region.Eval (instruction m) (extend (inputEnv m input) (encodeTuple m old))
      (header g) start (stepLabel m (g.step m input old)) (stepPayload m (g.step m input old)) start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.header_eval m g input old start

/-- Finite target continuation and counted source return from the same
carried tuple agree, including an exit with zero backedges. -/
theorem follow_iff (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Follow (instruction m) (inputEnv m input) (blocks g)
        0 (encodeTuple m old) start label payload finish ↔
      ∃ count result, g.ReturnsAfter m input count old result ∧
        label = 0 ∧ payload = packResult m result ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.follow_iff m g input old start finish label payload

theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) (inputEnv m input) (lower g) start label payload finish ↔
      ∃ result, g.Returns m input result ∧ label = 0 ∧ payload = packResult m result ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.lower_eval_iff m g input start finish label payload

theorem returns_iff (start : σ) (result : sortValue m.value out) :
    g.Returns m input result ↔
      Semantics.Region.Eval (instruction m) (inputEnv m input) (lower g) start 0 (packResult m result) start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.returns_iff m g input start result

theorem mem_denote_iff (start : σ) (result : sortValue m.value out) :
    result ∈ g.denote m input ↔
      Semantics.Region.Eval (instruction m) (inputEnv m input) (lower g) start 0 (packResult m result) start :=
  (g.returns_iff_mem_denote m input result).symm.trans (returns_iff g m input start result)

end Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic

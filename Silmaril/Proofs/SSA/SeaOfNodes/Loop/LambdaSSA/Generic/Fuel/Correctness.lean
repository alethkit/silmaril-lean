module

public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Proofs

open Diamond (Model Val ValueSort dataPorts)
open Diamond.LambdaSSA (Atom Primitive encode encodePort encodeTuple inputEnv instruction
  schedule terminatorRegion)
open RVSDG (Tuple)
open Isotope (Value)
open Isotope.LambdaSSA (Region Terminator)
open Isotope.LambdaSSA.Semantics (Env extend)
open Isotope.LambdaSSA.Semantics.Region (Eval)

universe u v w x

variable {σ : Type x}

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data} [DecidableEq Data]
variable (m : Model.{u, v, w} Op)

private theorem decodeValue_encode (sort : ValueSort Data) (value : Diamond.sortValue m.value sort) :
    decodeValue m sort (encode m (sort := sort) value) = some value := by
  cases sort with
  | data tag => simp [encode, decodeValue]
  | predicate =>
    cases value with
    | up b => cases b <;> rfl

private theorem decodeArgs_encode (sorts : List (ValueSort Data))
    (values : Tuple (Val m.value) (dataPorts sorts)) :
    decodeArgs m sorts (encodeTuple m values) = some values := by
  induction sorts with
  | nil => cases values; rfl
  | cons sort rest ih =>
    cases values with
    | cons value tail =>
      simp only [decodeArgs, encodeTuple, encodePort]
      rw [decodeValue_encode m sort value, ih tail]
      rfl

private theorem primitive_of_eval {op : Primitive Op} {arg result : Value (Atom m)}
    {start finish : σ} (h : instruction m op arg start result finish) :
    execPrimitive m op arg = some result := by
  cases op with
  | apply op =>
    obtain ⟨values, rfl, rfl, _⟩ := h
    simp [execPrimitive, decodeArgs_encode]

private theorem term_of_eval {env : Env (Atom m)} {term : Isotope.LambdaSSA.Tm (Primitive Op)}
    {result : Value (Atom m)} {start finish : σ}
    (h : Isotope.LambdaSSA.Semantics.Tm.Eval (instruction m) env term start result finish) :
    evalTerm m env term = some result := by
  induction h with
  | var | unit => rfl
  | op _ instruction ih => simp [evalTerm, ih, primitive_of_eval m instruction]
  | let₁ _ _ ihArg ihBody | let₂ _ _ ihArg ihBody
  | pair _ _ ihArg ihBody | case_inl _ _ ihArg ihBody | case_inr _ _ ihArg ihBody =>
    simp [evalTerm, ihArg, ihBody]
  | inl _ ih | inr _ ih => simp [evalTerm, ih]

private def Flat : Region (Primitive Op) → Prop
  | .br .. => True
  | .let₁ _ body | .let₂ _ body => Flat body
  | .case _ left right => Flat left ∧ Flat right
  | .cfg .. => False

private theorem flat_of_eval {env : Env (Atom m)} {r : Region (Primitive Op)}
    {label : Nat} {result : Value (Atom m)}
    {start finish : σ} (h : Eval (instruction m) env r start label result finish) (flat : Flat r) :
    evalFlat m env r = some (label, result) := by
  induction h using Eval.rec (motive_2 := fun _ {_} _ _ _ _ _ _ _ _ => True) with
  | br arg => simp [evalFlat, term_of_eval m arg]
  | let₁ arg _ ih | let₂ arg _ ih =>
    simp [evalFlat, term_of_eval m arg, ih flat]
  | case_inl arg _ ih => simp [evalFlat, term_of_eval m arg, ih flat.1]
  | case_inr arg _ ih => simp [evalFlat, term_of_eval m arg, ih flat.2]
  | cfg => exact False.elim flat
  | exit | step => trivial

omit [DecidableEq Data] in
private theorem flatTerminator (t : Terminator (Primitive Op)) :
    Flat (terminatorRegion t) := by
  induction t with
  | br => trivial
  | case _ _ _ ihLeft ihRight => exact ⟨ihLeft, ihRight⟩

omit [DecidableEq Data] in
private theorem flatSchedule {args : List (Diamond.Ty Data)} {past sigs : List (List (Diamond.Ty Data))}
    (flow : Diamond.Dataflow Op args past sigs)
    {context : List (Diamond.LambdaSSA.Code Data)}
    (layout : Diamond.LambdaSSA.Layout args past context)
    {tail : Region (Primitive Op)} (flat : Flat tail) :
    Flat (schedule flow layout tail) := by
  induction flow generalizing context with
  | nil => exact flat
  | cons _ _ _ ih => exact ih _

omit [DecidableEq Data] in
private theorem flatUnpack (ports : List (Diamond.Ty Data)) {tail : Region (Primitive Op)}
    (flat : Flat tail) : Flat (unpack ports tail) := by
  induction ports with
  | nil => exact flat
  | cons _ _ ih => exact ih

variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}
variable (g : Graph Op inputs carried entrySigs headerSigs out)
variable (input : Tuple (Val m.value) (dataPorts inputs))

private theorem entry_run :
    evalFlat m (inputEnv m input) (entry g) = some (0, encodeTuple m (g.initial m input)) :=
  flat_of_eval m (entry_eval g m input ()) (flatSchedule _ _ (flatTerminator _))

private theorem header_run (old : Tuple (Val m.value) (dataPorts carried)) :
    evalFlat m (extend (inputEnv m input) (encodeTuple m old)) (header g) =
      some (stepLabel m (g.step m input old), stepPayload m (g.step m input old)) :=
  flat_of_eval m (header_eval g m input old ())
    (flatUnpack _ (flatSchedule _ _ (flatTerminator _)))

private theorem follow_succ (budget : Nat) (old : Tuple (Val m.value) (dataPorts carried)) :
    follow m (inputEnv m input) (blocks g) (budget + 1) (0, encodeTuple m old) =
      (g.evalFrom m input budget old).map (fun result => (0, packResult m result)) := by
  induction budget generalizing old with
  | zero =>
    rw [follow, dite_eq_left (by decide), show blocks g ⟨0, by decide⟩ = header g from rfl,
      header_run m g input old, Graph.evalFrom]
    cases g.step m input old <;> rfl
  | succ budget ih =>
    rw [follow, dite_eq_left (by decide), show blocks g ⟨0, by decide⟩ = header g from rfl,
      header_run m g input old, Graph.evalFrom]
    cases g.step m input old with
    | inl result => rfl
    | inr next => exact ih next

theorem run_succ (budget : Nat) :
    run m (inputEnv m input) (budget + 1) (lower g) =
      (g.evalBackedges m budget input).map (fun result => (0, packResult m result)) := by
  rw [lower, run, entry_run m g input]
  exact follow_succ m g input budget _

theorem run_zero : run m (inputEnv m input) 0 (lower g) = none := by
  rw [lower, run, entry_run m g input]
  rfl

end Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Proofs

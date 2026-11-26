module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Semantics

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Interaction

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.SSA.LambdaRTL
open Silmaril.Elgot (iter liftPure mapReturn flattenBody flatten)
open Silmaril.Elgot.ITree (Tree diverge diverge_bind iterate_fixpoint iterate_naturality iterate_uniformity iterate_codiagonal)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (splitTransfer Transfer BlockInput)
open LetCase.LocallyNameless (Tm)
open Morphism.CaseSSA (erase)

universe u v

variable {E : Type u → Type u} {F : Type v} {V K α : Type (u + 1)}
variable {n labels : Nat}
variable (instr : LambdaSSA.Semantics.Interaction.Primitive E F α)

local notation "evalTerm" => LambdaSSA.Semantics.Interaction.term
local notation "evalRegion" => LambdaSSA.Semantics.Interaction.region

private theorem tree_value (src : Val V) {names : Names V n} {target : Tm Empty F n}
    (compiled : value names src = some target)
    {store : V → Value α} {env : Env α} (agrees : Agrees names store env) :
    evalTerm instr env (erase target) = pure (src.eval (treeModel instr) store) := by
  induction src generalizing target with
  | var reg =>
    obtain ⟨slot, found, rfl⟩ := Option.map_eq_some_iff.mp compiled
    exact congrArg pure (agrees reg slot found)
  | unit =>
    cases compiled
    rfl
  | pair left right ihLeft ihRight =>
    simp only [value, Option.bind_eq_some_iff, Option.map_eq_some_iff] at compiled
    obtain ⟨a, ha, b, hb, rfl⟩ := compiled
    simp only [erase, LambdaSSA.Semantics.Interaction.term, ihLeft ha, ihRight hb, pure_bind]
    rfl

private theorem tree_operand (src : Op V F) {names : Names V n} {target : Tm Empty F n}
    (compiled : operand names src = some target)
    {store : V → Value α} {env : Env α} (agrees : Agrees names store env) :
    evalTerm instr env (erase target) = src.eval (treeModel instr) store := by
  cases src with
  | val v => exact tree_value instr v compiled agrees
  | app f arg =>
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp compiled
    simp only [erase, LambdaSSA.Semantics.Interaction.term, tree_value instr arg ha agrees, pure_bind]
    rfl
  | inl | inr | abort => cases compiled

variable [DecidableEq V]

private theorem tree_terminal (index : K → Option (Fin labels)) (src : CFG.Term V K F)
    {n : Nat} {names : Names V n} {target : LambdaSSA.Flat F labels n}
    (compiled : term index names src = some target)
    {store : V → Value α} {env : Env α} (agrees : Agrees names store env) :
    (src.exec (treeModel instr) (fun label arg _ => pure (label, arg)) store >>=
      fun p => pure (treeNumber index p)) = evalRegion instr env target.erase := by
  induction src generalizing n names store env with
  | br label arg =>
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at compiled
    obtain ⟨i, numbered, a, ha, rfl⟩ := compiled
    simp only [CFG.Term.exec, LambdaSSA.Flat.erase, LambdaSSA.Semantics.Interaction.region, tree_value instr arg ha agrees,
      pure_bind, treeNumber, numbered, Option.map_some, Option.getD_some]
  | case op x left y right ihLeft ihRight =>
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at compiled
    obtain ⟨e, he, l, hl, r, hr, rfl⟩ := compiled
    simp only [CFG.Term.exec, LambdaSSA.Flat.erase, LambdaSSA.Semantics.Interaction.region, tree_operand instr op he agrees,
      bind_assoc]
    congr 1
    funext reply
    cases reply with
    | inl a =>
      simp only [treeModel, pure_bind]
      exact ihLeft hl (agrees_bind agrees x a)
    | inr b =>
      simp only [treeModel, pure_bind]
      exact ihRight hr (agrees_bind agrees y b)
    | _ => simp only [treeModel, diverge_bind]

private theorem tree_body (index : K → Option (Fin labels)) (src : CFG.Body V K F)
    {n : Nat} {names : Names V n} {target : LambdaSSA.Flat F labels n}
    (compiled : body index names src = some target)
    {store : V → Value α} {env : Env α} (agrees : Agrees names store env) :
    (src.evalJump (treeModel instr) store >>= fun p => pure (treeNumber index p)) =
      evalRegion instr env target.erase := by
  induction src generalizing n names store env with
  | term tail => exact tree_terminal instr index tail compiled agrees
  | let1 x op rest ih =>
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at compiled
    obtain ⟨a, ha, b, hb, rfl⟩ := compiled
    simp only [CFG.Body.evalJump, CFG.Body.exec, LambdaSSA.Flat.erase, LambdaSSA.Semantics.Interaction.region,
      tree_operand instr op ha agrees, bind_assoc]
    congr 1
    funext reply
    exact ih hb (agrees_bind agrees x reply)
  | let2 x y op rest ih =>
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at compiled
    obtain ⟨a, ha, b, hb, rfl⟩ := compiled
    simp only [CFG.Body.evalJump, CFG.Body.exec, LambdaSSA.Flat.erase, LambdaSSA.Semantics.Interaction.region,
      tree_operand instr op ha agrees, bind_assoc]
    congr 1
    funext reply
    cases reply with
    | pair a b =>
      simp only [treeModel, pure_bind]
      exact ih hb (agrees_bind (agrees_bind agrees x a) y b)
    | _ => simp only [treeModel, diverge_bind]

variable [DecidableEq K]

theorem entry_tree (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (store : V → Value α) (env : Env α)
    (inputs : ∀ i : Fin n, env i.val = store (captures i)) :
    (graph.entry.evalJump (treeModel instr) store >>= fun p => pure (treeNumber (labelIndex graph.blocks exits) p)) =
      evalRegion instr env target.entry.erase := by
  simp only [elaborate, Option.bind_eq_some_iff, Option.map_eq_some_iff] at accepted
  obtain ⟨entry, compiled, blocks, _, rfl⟩ := accepted
  apply tree_body instr _ _ compiled
  intro name slot found
  unfold first at found
  have eq : captures slot = name :=
    of_decide_eq_true (List.find?_some (p := fun i : Fin n => decide (captures i = name)) found)
  simpa [eq] using inputs slot

theorem block_tree (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (i : Fin graph.blocks.length) (store : V → Value α) (env : Env α) (payload : Value α) :
    (graph.blocks[i].2.body.evalJump (treeModel instr) (upd store graph.blocks[i].2.param payload) >>=
      fun p => pure (treeNumber (labelIndex graph.blocks exits) p)) =
      evalRegion instr (extend env payload) (target.block i).erase := by
  simp only [elaborate, Option.bind_eq_some_iff, Option.map_eq_some_iff] at accepted
  obtain ⟨entry, _, blocks, compiled, rfl⟩ := accepted
  apply tree_body instr _ _ (tabulate_at compiled i)
  have hidden : Agrees (fun (_ : V) => (none : Option (Fin n))) store env := by
    intro _ _ impossible
    cases impossible
  exact agrees_bind hidden _ payload

theorem step_tree (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (label : K) (i : Fin graph.blocks.length)
    (hit : graph.blocks.findFinIdx? (fun item => label == item.1) = some i)
    (store : V → Value α) (env : Env α) (payload : Value α) :
    (CFG.Cyclic.stepSSA (treeModel instr) graph.blocks store (label, payload) >>=
      fun s => pure (s.map id (treeNumber (labelIndex graph.blocks exits)))) =
      (evalRegion instr (extend env payload) (target.block i).erase >>= fun p => pure (.inr p)) := by
  have found : graph.blocks.lookup label = some graph.blocks[i].2 := by
    rw [lookup_index, hit]
    rfl
  simp only [CFG.Cyclic.stepSSA, found, ← bind_pure_comp, bind_assoc, pure_bind, Sum.map_inr]
  rw [← block_tree instr graph exits captures accepted i store env payload]
  simp only [bind_assoc, pure_bind]

/-- A loop may route a completed block to one final, pure exit step. -/
private theorem iterate_delayed {A B : Type (u + 1)} (f : A → Tree E (B ⊕ A)) :
    iter (fun p : B ⊕ A => Sum.elim (pure ∘ Sum.inl)
      (fun a => f a >>= fun next => pure (Sum.inr next)) p) =
      Sum.elim pure (iter f) := by
  let branch : B ⊕ A → (B ⊕ (B ⊕ A)) ⊕ (B ⊕ A)
    | .inl b => .inr (.inl b)
    | .inr a => .inl (.inr (.inr a))
  let step : B ⊕ A → Tree E ((B ⊕ (B ⊕ A)) ⊕ (B ⊕ A))
    | .inl b => pure (.inl (.inl b))
    | .inr a => f a >>= fun next => pure (branch next)
  have atExit (b : B) : iter step (.inl b) = pure (.inl b) := by
    rw [congrFun (iterate_fixpoint step) (.inl b)]
    simp [step]
  have first (a : A) : iter step (.inr a) = (f a >>= fun s => pure (s.map id Sum.inr)) := by
    rw [congrFun (iterate_fixpoint step) (.inr a)]
    change ((f a >>= fun next => pure (branch next)) >>= Sum.elim pure (iter step)) = _
    simp only [bind_assoc, pure_bind]
    congr 1
    funext s
    cases s <;> simp only [branch, Sum.elim_inl, Sum.elim_inr, Sum.map_inl, Sum.map_inr, id_eq, atExit]
  have flat : flattenBody step = fun p => Sum.elim (pure ∘ Sum.inl)
      (fun a => f a >>= fun next => pure (Sum.inr next)) p := by
    funext p
    cases p with
    | inl b => simp [flattenBody, Bind.kleisliRight, liftPure, step, flatten]
    | inr a =>
      simp only [flattenBody, Bind.kleisliRight, liftPure, step, bind_assoc, pure_bind, Function.comp_apply,
        Sum.elim_inr]
      congr 1
      funext s
      cases s <;> rfl
  have inner := iterate_uniformity f (iter step) Sum.inr (by
    funext a
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, first]
    rfl)
  rw [← flat, ← iterate_codiagonal step]
  funext p
  cases p with
  | inl b =>
    rw [congrFun (iterate_fixpoint (iter step)) (.inl b)]
    simp [atExit]
  | inr a =>
    simpa [Bind.kleisliRight, liftPure] using (congrFun inner a).symm

omit [DecidableEq V] in
private theorem split_number {label : K} {payload : Value α}
    (blocks : List (K × CFG.Block V K F)) (exits : List K) :
    splitTransfer blocks.length (treeNumber (labelIndex blocks exits) (label, payload)) =
      match blocks.findFinIdx? (fun item => label == item.1) with
      | some i => .inr (i, payload)
      | none => .inl (treeExitNumber exits (label, payload)) := by
  unfold labelIndex
  cases hit : blocks.findFinIdx? (fun item => label == item.1) with
  | some i => simp [treeNumber, splitTransfer, hit, i.isLt]
  | none =>
    cases ext : exits.findFinIdx? (fun exit => label == exit) with
    | none => simp [treeNumber, treeExitNumber, splitTransfer, hit, ext]
    | some e => simp [treeNumber, treeExitNumber, splitTransfer, hit, ext]

theorem run_tree (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (store : V → Value α) (env : Env α)
    (inputs : ∀ i : Fin n, env i.val = store (captures i)) :
    (CFG.Cyclic.runSSA (treeModel instr) graph store >>= fun p => pure (treeExitNumber exits p)) =
      evalRegion instr env target.erase := by
  let number := treeNumber (labelIndex graph.blocks exits) (α := α)
  let encode := splitTransfer graph.blocks.length ∘ number
  let namedStep := CFG.Cyclic.stepSSA (treeModel instr) graph.blocks store
  let indexedStep (p : BlockInput α graph.blocks.length) :=
    evalRegion instr (extend env p.2) (target.block p.1).erase >>= fun out =>
      pure (splitTransfer graph.blocks.length out)
  let delayed (p : Transfer α ⊕ BlockInput α graph.blocks.length) :=
    Sum.elim (pure ∘ Sum.inl) (fun b => indexedStep b >>= fun next => pure (.inr next)) p
  let numberedStep := mapReturn namedStep (fun p => pure (treeExitNumber exits p))
  have commute : (numberedStep >=> liftPure (Sum.map id encode)) = (liftPure encode >=> delayed) := by
    funext p
    rcases p with ⟨label, payload⟩
    have split := split_number (F := F) (V := V) (label := label) (payload := payload) graph.blocks exits
    cases hit : graph.blocks.findFinIdx? (fun item => label == item.1) with
    | none =>
      have found : graph.blocks.lookup label = none := by rw [lookup_index, hit]; rfl
      simp [numberedStep, namedStep, CFG.Cyclic.stepSSA, found, mapReturn, Bind.kleisliRight, liftPure,
        encode, number, delayed, split, hit]
    | some i =>
      have found : graph.blocks.lookup label = some graph.blocks[i].2 := by rw [lookup_index, hit]; rfl
      simp only [numberedStep, namedStep, CFG.Cyclic.stepSSA, found, ← bind_pure_comp, mapReturn,
        Bind.kleisliRight, liftPure, Function.comp_apply, bind_assoc, pure_bind, Sum.elim_inr, Sum.map_inr]
      have atBlock : encode (label, payload) = .inr (i, payload) := split.trans (by rw [hit])
      rw [atBlock]
      simp only [delayed, indexedStep, Sum.elim_inr, bind_assoc, pure_bind]
      rw [← block_tree instr graph exits captures accepted i store env payload]
      simp only [bind_assoc, pure_bind]
      rfl
  have loop (p : K × Value α) :
      (iter namedStep p >>= fun q => pure (treeExitNumber exits q)) =
        Sum.elim pure (iter indexedStep) (encode p) := by
    calc
      _ = iter numberedStep p := congrFun (iterate_naturality namedStep _) p
      _ = iter delayed (encode p) := by
        simpa [Bind.kleisliRight, liftPure] using congrFun (iterate_uniformity _ _ _ commute) p
      _ = _ := congrFun (iterate_delayed indexedStep) (encode p)
  change (graph.entry.evalJump (treeModel instr) store >>= iter namedStep) >>= _ =
    (evalRegion instr env target.entry.erase >>= fun out =>
      Sum.elim pure (iter indexedStep) (splitTransfer graph.blocks.length out))
  rw [bind_assoc, ← entry_tree instr graph exits captures accepted store env inputs]
  simp only [bind_assoc, pure_bind]
  exact congrArg _ (funext loop)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Interaction

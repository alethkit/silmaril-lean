module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Thms
import Silmaril.SSA.LambdaRTL.CFG.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block Row Pending assign execute)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan Checked)
open Silmaril.Elgot.ITree (Tree)
open LambdaSSA.Semantics.Interaction (Primitive)
open LambdaSSA.FiniteCFG (packedTreeOutput)

universe u v
variable {V W K J α : Type (u + 1)} {F : Type v} {E : Type u → Type u}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
variable (plan : Plan V W K J) (instr : Primitive E F α)

/-- The first right transfer names the forwarding block on the split edge. -/
def routed (p : Pending V K (Value α)) : Pending W J (Value α) :=
  (match p.1 with
   | .returned value => .returned value
   | .jump pred target =>
       .jump (pred.map plan.label)
         (if plan.selected pred target then plan.forward else plan.label target),
   plan.renameStore p.2)

/-- The right transfer after the optional forwarding hop. -/
def aligned (p : Pending V K (Value α)) : Pending W J (Value α) :=
  (match p.1 with
   | .returned value => .returned value
   | .jump pred target => .jump (plan.rekey target pred) (plan.label target),
   plan.renameStore p.2)

omit [DecidableEq K] [DecidableEq J] in
private theorem update {β : Type (u + 1)} (store : V → β) (x : V) (value : β) :
    upd (plan.renameStore store) (plan.register x) value =
      plan.renameStore (upd store x value) := by
  funext y
  obtain ⟨y, rfl⟩ := plan.register.surjective y
  simp [Plan.renameStore, upd]

omit [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] in
private theorem val_eval (store : V → Value α) (value : Val V) :
    (value.rename plan.register).eval (treeModel instr) (plan.renameStore store) =
      value.eval (treeModel instr) store := by
  induction value with
  | var x => simp [Val.rename, Val.eval, Plan.renameStore]
  | unit => rfl
  | pair a b ihA ihB => simp only [Val.rename, Val.eval, ihA, ihB]

omit [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] in
private theorem op_eval (store : V → Value α) (op : Op V F) :
    (op.rename plan.register).eval (treeModel instr) (plan.renameStore store) =
      op.eval (treeModel instr) store := by
  cases op <;> simp [Op.rename, Op.eval, val_eval]

omit [DecidableEq K] [DecidableEq J] in
private theorem term_exec {β : Type (u + 1)} (route : Option K → Option J)
    (next : Option J → Value α → (W → Value α) → Tree E β)
    (term : CFG.Term V (Option K) F) (store : V → Value α) :
    (plan.renameTerm route term).exec (treeModel instr) next (plan.renameStore store) =
      term.exec (treeModel instr) (fun k a s => next (route k) a (plan.renameStore s)) store := by
  induction term generalizing store with
  | br key value => simp [Plan.renameTerm, CFG.Term.exec, val_eval]
  | case op x left y right ihL ihR =>
    simp only [Plan.renameTerm, CFG.Term.exec, op_eval, update]
    congr 1
    funext branch
    cases branch <;> simp [ihL, ihR]

omit [DecidableEq K] [DecidableEq J] in
private theorem body_exec {β : Type (u + 1)} (route : Option K → Option J)
    (next : Option J → Value α → (W → Value α) → Tree E β)
    (body : CFG.Body V (Option K) F) (store : V → Value α) :
    (plan.renameBody route body).exec (treeModel instr) next (plan.renameStore store) =
      body.exec (treeModel instr) (fun k a s => next (route k) a (plan.renameStore s)) store := by
  induction body generalizing store with
  | term term => exact term_exec plan instr route next term store
  | let1 x op body ih => simp [Plan.renameBody, CFG.Body.exec, op_eval, update, ih]
  | let2 x y op body ih => simp [Plan.renameBody, CFG.Body.exec, op_eval, update, ih]

omit [DecidableEq J] in
private theorem execute_routed (pred : Option K) (body : CFG.Body V (Option K) F)
    (store : V → Value α) :
    execute (treeModel instr) (pred.map plan.label) (plan.renameBody (plan.route pred) body)
        (plan.renameStore store) =
      routed plan <$> execute (treeModel instr) pred body store := by
  unfold execute
  rw [body_exec, CFG.Body.exec_eq_evalRTL, CFG.Body.exec_eq_evalRTL]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  congr 1
  funext result
  obtain ⟨key, value, nextStore⟩ := result
  cases key <;> simp [routed, Plan.route]

omit [DecidableEq V] [DecidableEq W] [DecidableEq J] in
private theorem rekey_injective (target : K) : Function.Injective (plan.rekey target) := by
  intro a b equal
  by_cases ha : plan.selected a target <;> by_cases hb : plan.selected b target
  · exact (ha.1).trans hb.1.symm
  · cases b with
    | none => simp [Plan.rekey, ha, hb] at equal
    | some b => simp [Plan.rekey, ha, hb, Ne.symm (plan.fresh b)] at equal
  · cases a with
    | none => simp [Plan.rekey, ha, hb] at equal
    | some a => simp [Plan.rekey, ha, hb, plan.fresh a] at equal
  · exact Option.map_injective plan.label.injective (by simpa [Plan.rekey, ha, hb] using equal)

omit [DecidableEq V] [DecidableEq W] in
private theorem lookup_column (target : K) (pred : Option K) (entries : List (Option K × Val V)) :
    (entries.map fun (k, value) => (plan.rekey target k, value.rename plan.register)).lookup
        (plan.rekey target pred) =
      (entries.lookup pred).map (Val.rename plan.register) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨key, value⟩ := entry
    by_cases hit : pred = key
    · subst key
      simp
    · have missed := beq_eq_false_iff_ne.mpr hit
      have mappedMiss := beq_eq_false_iff_ne.mpr (fun equal => hit (rekey_injective plan target equal))
      simp only [List.map_cons, List.lookup_cons, missed, mappedMiss, ih]

private theorem assigned (target : K) (pred : Option K) (rows : List (Row V K))
    (snapshot store : V → Value α) :
    assign (treeModel instr) (plan.rekey target pred) (plan.renameStore snapshot)
        (rows.map (plan.renameRow target)) (plan.renameStore store) =
      plan.renameStore (assign (treeModel instr) pred snapshot rows store) := by
  induction rows generalizing store with
  | nil => rfl
  | cons row rows ih =>
    have read :
        (plan.renameRow target row).operand (plan.rekey target pred) =
          (row.operand pred).rename plan.register := by
      unfold Plan.renameRow Row.operand
      rw [lookup_column]
      cases row.incoming.lookup pred <;> rfl
    simp only [List.map_cons, assign, read, val_eval]
    change assign (treeModel instr) _ _ _ (upd (plan.renameStore store) (plan.register row.dst) _) = _
    rw [update, ih]

omit [DecidableEq V] [DecidableEq W] in
private theorem lookup_renamed (source : Graph V K F) (target : K) :
    (plan.rewrite source).blocks.lookup (plan.label target) =
      (source.blocks.lookup target).map (plan.renameBlock target) := by
  change (source.blocks.flatMap _).lookup (plan.label target) = _
  induction source.blocks with
  | nil => rfl
  | cons entry entries ih =>
    obtain ⟨key, block⟩ := entry
    have missesForward := beq_eq_false_iff_ne.mpr (plan.fresh target)
    by_cases same : target = key
    · subst key
      by_cases isHeader : target = plan.header
      · simp [List.lookup_cons, isHeader, beq_eq_false_iff_ne.mpr (plan.fresh plan.header)]
      · simp [isHeader]
    · by_cases isHeader : key = plan.header
      · subst key
        have missed := beq_eq_false_iff_ne.mpr same
        have mappedMiss := beq_eq_false_iff_ne.mpr (fun equal => same (plan.label.injective equal))
        simp only [List.flatMap_cons, ↓reduceIte, List.cons_append, List.nil_append,
          List.lookup_cons, missed, mappedMiss, missesForward, ih]
      · have missed := beq_eq_false_iff_ne.mpr same
        have mappedMiss := beq_eq_false_iff_ne.mpr (fun equal => same (plan.label.injective equal))
        simp only [List.flatMap_cons, isHeader, ite_false, List.cons_append, List.nil_append,
          List.lookup_cons, missed, mappedMiss, ih]

omit [DecidableEq V] [DecidableEq W] in
private theorem lookup_forward (source : Graph V K F)
    (present : (source.blocks.lookup plan.header).isSome = true) :
    (plan.rewrite source).blocks.lookup plan.forward = some plan.forwardBlock := by
  change (source.blocks.flatMap _).lookup plan.forward = _
  generalize source.blocks = blocks at *
  induction blocks with
  | nil => simp at present
  | cons entry entries ih =>
    obtain ⟨key, block⟩ := entry
    by_cases isHeader : key = plan.header
    · simp [isHeader]
    · have missesForward := beq_eq_false_iff_ne.mpr (Ne.symm (plan.fresh key))
      have missed := beq_eq_false_iff_ne.mpr (Ne.symm isHeader)
      simp only [List.flatMap_cons, isHeader, ite_false, List.cons_append,
        List.nil_append, List.lookup_cons, missesForward]
      apply ih
      simpa only [List.lookup_cons, missed] using present

omit [DecidableEq J] in
theorem entry_routed (source : Graph V K F) (store : V → Value α) :
    entryTree instr (plan.rewrite source) (plan.renameStore store) =
      Sum.map id (routed plan) <$> entryTree instr source store := by
  simp only [entryTree, Plan.rewrite]
  have renamed := execute_routed plan instr none source.entry store
  simp only [Option.map_none] at renamed
  rw [renamed]
  simp [Functor.map_map]

theorem step_aligned (source : Graph V K F) (p : Pending V K (Value α)) :
    stepTree instr (plan.rewrite source) (aligned plan p) =
      Sum.map id (routed plan) <$> stepTree instr source p := by
  obtain ⟨control, store⟩ := p
  cases control with
  | returned value => simp [aligned, step_return]
  | jump pred target =>
    cases old : source.blocks.lookup target with
    | none =>
      have missing : (plan.rewrite source).blocks.lookup (plan.label target) = none := by
        rw [lookup_renamed, old]
        rfl
      simp [aligned, stepTree, Elgot.mapReturn, CFG.Cyclic.Phi.step, old, missing,
        treeExitNumber, treeNumber, packedTreeOutput]
    | some block =>
      have new : (plan.rewrite source).blocks.lookup (plan.label target) =
          some (plan.renameBlock target block) := by
        rw [lookup_renamed, old]
        rfl
      simp only [aligned, step_jump instr source pred target store old, step_jump instr _ _ _ _ new,
        Plan.renameBlock, assigned]
      have renamed := execute_routed plan instr (some target) block.body
        (assign (treeModel instr) pred store block.rows store)
      simp only [Option.map_some] at renamed
      rw [renamed]
      simp [Functor.map_map]

omit [DecidableEq V] in
theorem step_forward (source : Graph V K F) (checked : plan.hasBackedge source = true)
    (store : V → Value α) :
    stepTree instr (plan.rewrite source) (.jump (some (plan.label plan.header)) plan.forward,
      plan.renameStore store) =
      pure (.inr (.jump (some plan.forward) (plan.label plan.header), plan.renameStore store)) := by
  have present : (source.blocks.lookup plan.header).isSome = true := by
    cases h : source.blocks.lookup plan.header <;> simp_all [Plan.hasBackedge]
  rw [step_jump instr _ _ _ _ (lookup_forward plan source present)]
  simp [Plan.forwardBlock, assign, execute, CFG.Body.exec, CFG.Term.exec, CFG.Cyclic.Phi.br]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split

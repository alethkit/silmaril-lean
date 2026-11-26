module

public import Silmaril.SSA.SeaOfNodes.Loop.Theta.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.ThetaProofs

open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts sortValue)
open RVSDG (Locals Port Tuple Wires extend)
open RVSDG.NestedTheta (Term identityPorts)

universe u v w a b c

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable {g : Graph Op inputs carried entrySigs headerSigs out} {m : Model.{u, v, w} Op}

private theorem map_map {T : Type u} {F : T → Type a} {G : T → Type b} {H : T → Type c} {ts : List T}
    (xs : Tuple F ts) (f : ∀ t, F t → G t) (h : ∀ t, G t → H t) :
    (xs.map f).map h = xs.map (fun t x => h t (f t x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [Tuple.map, ih]

private theorem identity_read {T : Type u} {F : T → Type w} {ts : List T} (xs : Tuple F ts) :
    (identityPorts ts).map (fun _ p => xs.get p) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [identityPorts, Tuple.map, map_map, Tuple.get, ih]

private theorem argWires_read {T : Type u} {F : T → Type w}
    {args : List T} {past : List (List T)} (entry : Tuple F args) (locals : Locals F past) :
    (argWires args past).read entry locals = entry := by
  simp only [argWires, Wires.read, map_map]
  exact identity_read entry

private theorem read_append {T : Type u} {F : T → Type w}
    {args left right : List T} {past : List (List T)}
    (xs : Wires args past left) (ys : Wires args past right)
    (entry : Tuple F args) (locals : Locals F past) :
    Wires.read (appendTuple ys xs) entry locals =
      appendTuple (ys.read entry locals) (xs.read entry locals) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [appendTuple, Wires.read, Tuple.map] at ih ⊢
    rw [ih]

private theorem split_append {T : Type u} {F : T → Type w} {left right : List T}
    (xs : Tuple F left) (ys : Tuple F right) :
    splitTuple left (appendTuple ys xs) = (xs, ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [splitTuple, appendTuple, ih]

private theorem lastPort_read {F : Ty Data → Type w}
    {head : List (Ty Data)} {past : List (List (Ty Data))} {t : Ty Data}
    (p : Port head t) (locals : Locals F past) (xs : Tuple F head) :
    ((locals.snoc xs).get (Diamond.lastIndex head past)).get
      (Diamond.lastPort p past) = xs.get p := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact ih locals.2

private theorem allLastWires_read {args head : List (Ty Data)}
    {F : Ty Data → Type w} {past : List (List (Ty Data))}
    (entry : Tuple F args) (locals : Locals F past) (xs : Tuple F head) :
    (allLastWires past).read entry (locals.snoc xs) = xs := by
  simp only [allLastWires, Diamond.lastWires, Wires.read, map_map, lastPort_read]
  exact identity_read xs

private theorem lowerFlow_exec {args results : List (Ty Data)}
    {past sigs tail : List (List (Ty Data))}
    (m : Model.{u, v, w} Op) (flow : Dataflow Op args past sigs)
    (rest : Term (ThetaOpcode Op) args (extend past sigs) tail results)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (output : Tuple (Val m.value) results) :
    (lowerFlow flow rest).Exec (thetaRuntime m) entry locals output ↔
      rest.Exec (thetaRuntime m) entry (flow.eval m entry locals) output := by
  induction flow with
  | nil => rfl
  | cons op wires more ih =>
    simp only [lowerFlow, Term.Exec, RVSDG.NestedTheta.Kind.Exec, Diamond.Dataflow.eval,
      thetaRuntime, exists_eq_left']
    exact ih rest _

private abbrev CarrierVal (m : Model.{u,v,w} Op) (inputs carried : List (ValueSort Data)) :=
  Tuple (Val m.value) (headerPorts inputs carried)

private abbrev BodyExec (g : Graph Op inputs carried entrySigs headerSigs out)
    (m : Model.{u,v,w} Op) (before : CarrierVal m inputs carried) (again : Bool)
    (after : CarrierVal m inputs carried) : Prop :=
  g.thetaBody.Returns (thetaRuntime m) before (RVSDG.Theta.bodyResult (thetaRuntime m) again after)

private def exitValue (g : Graph Op inputs carried entrySigs headerSigs out) (m : Model.{u,v,w} Op)
    (state : CarrierVal m inputs carried) : sortValue m.value out :=
  Diamond.read m g.result state (g.header.eval m state PUnit.unit)

private theorem body_result_eq {ports : List (Ty Data)} (a b : Bool)
    (xs ys : Tuple (Val m.value) ports) :
    RVSDG.Theta.bodyResult (thetaRuntime m) a xs = RVSDG.Theta.bodyResult (thetaRuntime m) b ys ↔
      b = a ∧ ys = xs := by
  constructor
  · intro eq
    let tag (t : Tuple (Val m.value) (RVSDG.Theta.BodyResults ports)) : Fin 2 := (t.get .head).down
    let payload (t : Tuple (Val m.value) (RVSDG.Theta.BodyResults ports)) : Tuple (Val m.value) ports :=
      match t with | .cons _ rest => rest
    have htag := congrArg tag eq
    have hab : b = a := by cases a <;> cases b <;> first | rfl | cases htag
    exact ⟨hab, (congrArg payload eq).symm⟩
  · rintro ⟨rfl, rfl⟩
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem body_exec (input : Tuple (Val m.value) (dataPorts inputs))
    (old : Tuple (Val m.value) (dataPorts carried)) (again : Bool)
    (after : CarrierVal m inputs carried) :
    BodyExec g m (appendTuple old input) again after ↔
      match g.step m input old with
      | .inl _ => again = false ∧ after = appendTuple old input
      | .inr next => again = true ∧ after = appendTuple next input := by
  simp only [BodyExec, Graph.thetaBody, Term.Returns, Incoming.select]
  rw [lowerFlow_exec m g.header]
  simp only [Term.Exec, RVSDG.NestedTheta.Kind.Exec, exists_eq_left', allLastWires_read]
  let state := appendTuple old input
  let locals := g.header.eval m state PUnit.unit
  change (thetaRuntime m).run (.route inputs carried)
    (.cons (Diamond.read m g.predicate state locals)
      (Wires.read (appendTuple (g.phiInputs .backedge) (argWires _ _)) state locals)) =
        RVSDG.Theta.bodyResult (thetaRuntime m) again after ↔ _
  simp only [read_append, argWires_read, thetaRuntime, split_append]
  dsimp only [state, locals]
  simp only [split_append]
  simp only [Graph.step]
  cases (Diamond.read m g.predicate (appendTuple old input)
    (g.header.eval m (appendTuple old input) PUnit.unit)).down <;>
    simp only [Graph.latch, Bool.false_eq_true, ite_false, ite_true]
  · exact body_result_eq (m := m) (ports := headerPorts inputs carried) false again _ after
  · exact body_result_eq (m := m) (ports := headerPorts inputs carried) true again _ after

private theorem exit_value (input : Tuple (Val m.value) (dataPorts inputs))
    (old : Tuple (Val m.value) (dataPorts carried)) {result : sortValue m.value out}
    (taken : g.step m input old = .inl result) :
    exitValue g m (appendTuple old input) = result := by
  simp only [Graph.step] at taken
  split at taken
  · cases taken
  · exact Sum.inl.inj taken

private theorem theta_to_source (input : Tuple (Val m.value) (dataPorts inputs))
    {before after : CarrierVal m inputs carried} (run : RVSDG.Theta.Iterate (BodyExec g m) before after)
    (old : Tuple (Val m.value) (dataPorts carried)) (entry : before = appendTuple old input) :
    ∃ count, g.ReturnsAfter m input count old (exitValue g m after) := by
  induction run generalizing old with
  | stop last =>
    rw [entry, body_exec] at last
    cases step : g.step m input old with
    | inl value =>
      rw [step] at last
      exact ⟨0, .exit (step.trans (congrArg Sum.inl
        ((congrArg (exitValue g m) last.2).trans (exit_value input old step)).symm))⟩
    | inr next => simp [step] at last
  | again next _ ih =>
    rw [entry, body_exec] at next
    cases step : g.step m input old with
    | inl value => simp [step] at next
    | inr nextPhi =>
      rw [step] at next
      obtain ⟨n, run⟩ := ih nextPhi next.2
      exact ⟨n + 1, .backedge step run⟩

private theorem source_to_theta (input : Tuple (Val m.value) (dataPorts inputs))
    {old : Tuple (Val m.value) (dataPorts carried)} {count : Nat} {result : sortValue m.value out}
    (run : g.ReturnsAfter m input count old result) :
    ∃ after, RVSDG.Theta.Iterate (BodyExec g m) (appendTuple old input) after ∧
      exitValue g m after = result := by
  induction run with
  | exit taken =>
    exact ⟨_, .stop ((body_exec _ _ _ _).mpr (by rw [taken]; exact ⟨rfl, rfl⟩)),
      exit_value _ _ taken⟩
  | backedge taken _ ih =>
    obtain ⟨after, run, result⟩ := ih
    exact ⟨after, .again ((body_exec _ _ _ _).mpr (by rw [taken]; exact ⟨rfl, rfl⟩)) run, result⟩

set_option backward.isDefEq.respectTransparency false in
theorem lower_returns (g : Graph Op inputs carried entrySigs headerSigs out)
    (m : Model.{u,v,w} Op) (input : Tuple (Val m.value) (dataPorts inputs))
    (result : sortValue m.value out) :
    g.Returns m input result ↔ g.lowerTheta.Returns (thetaRuntime m) input (.cons result .nil) := by
  rw [Graph.lowerTheta, RVSDG.NestedTheta.Term.returns_toGraph]
  simp only [Graph.lowerThetaTerm, Term.Returns, Incoming.select]
  rw [lowerFlow_exec m g.preheader]
  simp only [Term.Exec, RVSDG.NestedTheta.Kind.Exec, read_append, argWires_read,
    exists_eq_left', allLastWires_read]
  change g.Returns m input result ↔
    ∃ after, RVSDG.Theta.Iterate (BodyExec g m) (appendTuple (g.initial m input) input) after ∧
      (Tuple.cons (exitValue g m after) .nil : Tuple (Val m.value) [.value out]) = .cons result .nil
  constructor
  · rintro ⟨_, run⟩
    obtain ⟨after, run, value⟩ := source_to_theta input run
    exact ⟨after, run, congrArg (fun x => Tuple.cons x .nil) value⟩
  · rintro ⟨after, run, value⟩
    have returned := theta_to_source input run (g.initial m input) rfl
    have same : exitValue g m after = result :=
      congrArg (fun xs : Tuple (Val m.value) [.value out] => xs.get .head) value
    rw [same] at returned
    exact returned

end Silmaril.SSA.SeaOfNodes.Loop.ThetaProofs

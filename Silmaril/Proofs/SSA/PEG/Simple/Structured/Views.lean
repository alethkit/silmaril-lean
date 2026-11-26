module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Guard

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before mid after vars inside all : List (Ty Data)} {t : Ty Data}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params} {read : Reads m all}

/-- The rows of a fragment embedded in a final table. All enclosing loop
addresses precede the fragment, so its fresh pass address is outside the
fixed coordinates. -/
structure View (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params) (read : Reads m all)
    (active : List (Fin all.length)) (code : Code P params before after) where
  holes : Rows P params before all
  embed : Embed after all
  offset : Nat
  address : ∀ t (r : Port after t), pos (embed r) = offset + pos r
  older : ∀ l ∈ active, l.val < offset
  eqs : Equations m env (code.rows holes embed active.head?) embed read

variable {active : List (Fin all.length)}

@[expose] noncomputable def View.left {a : Code P params before mid} {b : Code P params mid after}
    (view : View m env read active (.seq a b)) : View m env read active a :=
  let k := (codeShift b).choose
  { holes := view.holes
    embed := fun r => view.embed (b.lift r)
    offset := view.offset + k
    address := by
      intro t r
      rw [view.address, (codeShift b).choose_spec, Nat.add_assoc]
    older := by
      intro l member
      exact Nat.lt_of_lt_of_le (view.older l member) (Nat.le_add_right _ _)
    eqs := seqLeft m env a b view.holes view.embed active.head? read view.eqs }

@[expose] def View.right {a : Code P params before mid} {b : Code P params mid after}
    (view : View m env read active (.seq a b)) : View m env read active b :=
  { holes := a.rows view.holes (fun r => view.embed (b.lift r)) active.head?
    embed := view.embed
    offset := view.offset
    address := view.address
    older := view.older
    eqs := view.eqs }

variable {init : Tuple (Port before) vars} {body : Code P params (vars ++ before) inside}
variable {guard : Port inside .bool} {next : Tuple (Port inside) vars} {neg : P [.bool] .bool}

@[expose] def View.key (view : View m env read active (.loop init body guard next neg)) :
    Fin all.length :=
  (numberPort (view.embed (passRef vars))).id

theorem View.key_fresh (view : View m env read active (.loop init body guard next neg))
    {l : Fin all.length} (h : l ∈ active) : l ≠ view.key := by
  have key : view.key.val = view.offset + vars.length := by
    change pos (view.embed (passRef vars)) = _
    rw [view.address, posPass]
  have lt := view.older l h
  intro eq
  subst l
  omega

@[expose] def View.inner (view : View m env read active (.loop init body guard next neg)) :
    View m env read (view.key :: active) body where
  holes := loopHoles body init next view.holes view.embed
  embed := fun r => view.embed (insideRef vars r)
  offset := view.offset + vars.length + 2
  address := by
    intro t r
    rw [view.address, posInside]
    omega
  older := by
    intro l mem
    rcases List.mem_cons.mp mem with rfl | old
    · change pos (view.embed (passRef vars)) < _
      rw [view.address, posPass]
      omega
    · have := view.older l old
      omega
  eqs := by
    intro i t r
    have h := view.eqs i t (insideRef vars r)
    change _ = rowValue m env (loopRows body guard neg active.head? view.embed
      (body.rows (loopHoles body init next view.holes view.embed)
        (fun r => view.embed (insideRef vars r)) (some view.key)) (insideRef vars r)) read i at h
    rw [loopRows_inside] at h
    exact h

/-- All indices that agree at the enclosing loop coordinates of the fragment. -/
@[expose] def Agrees {n : Nat} (active : List (Fin n)) (fixed i : Index n) : Prop :=
  ∀ l ∈ active, i l = fixed l

theorem agrees_set (view : View m env read active (.loop init body guard next neg))
    {fixed i : Index all.length} (agrees : Agrees active fixed i) (k : Nat) :
    Agrees active fixed (i.set view.key k) := by
  intro l member
  rw [Index.set, ite_eq_right (view.key_fresh member)]
  exact agrees l member

theorem agrees_self (active : List (Fin all.length)) (i : Index all.length) :
    Agrees active i i :=
  fun _ _ => rfl

@[expose] def RealizesAt (read : Reads m all) (embed : Embed before all)
    (ctx : Tuple (Port before) vars) (store : Tuple m.Value vars) (i : Index all.length) : Prop :=
  ∀ t (r : Port vars t), read (embed (ctx.get r)) i = some (store.get r)

@[expose] def RealizesOn (read : Reads m all) (embed : Embed before all)
    (ctx : Tuple (Port before) vars) (store : Tuple m.Value vars)
    (active : List (Fin all.length)) (fixed : Index all.length) : Prop :=
  ∀ i, Agrees active fixed i → RealizesAt read embed ctx store i

/-- The seed used to run straight code is the graph's pointwise valuation
of the old context. -/
@[expose] noncomputable def View.seed {code : Simple.Code P params before after}
    (view : View m env read active (.straight code)) (i : Index all.length) :
    Simple.Proofs.NodeValues m before :=
  (ports before).map fun _ r => read (view.embed (code.lift r)) i

theorem View.straightRead {code : Simple.Code P params before after}
    (view : View m env read active (.straight code)) (i : Index all.length) (r : Port after t) :
    read (view.embed r) i = (code.eval m env (view.seed i)).get r := by
  apply straightEval m env code view.holes view.embed read i (view.seed i)
  · intro t r
    unfold View.seed
    rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
  · exact view.eqs

theorem View.seedRealizes {code : Simple.Code P params before after}
    (view : View m env read active (.straight code)) {ctx : Tuple (Port before) vars}
    {store : Tuple m.Value vars} {i : Index all.length}
    (entry : RealizesAt read (fun r => view.embed (code.lift r)) ctx store i) :
    Realizes m (view.seed i) ctx store := by
  intro t r
  unfold View.seed
  rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
  exact entry t r

end Silmaril.SSA.PEG.Simple.Structured.Proofs

module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Model.Defs
import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

/-! # Continuation semantics of the explicit acyclic compiler -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open OrderedTheta (carried results carriedData resultData pack point)
open OrderedRuntime.Structured
open TwoBlock.TwoExit (callCase Pure)
open LinearChain.Wiring (newest)
open Wiring (Code Tail emit eval WireValues)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B X Y S : τ}

variable {args ins out outs : Ports (OrderedRuntime.Structured.Ty τ)}
variable {past : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {a : Data args} {o : Data outs}
variable {live : Origin (Threaded args) past runtime}

local notation "readWire" => OrderedRuntime.Structured.readOrigin (F := WireValues (τ := τ) (σ := σ))

omit [TypeFormers τ] [Isotope.Subtyping τ] [TypeModel τ] in
@[simp] theorem read_newest {F : OrderedRuntime.Structured.Ty τ → Type u}
    {t : OrderedRuntime.Structured.Ty τ} (p : Port out t)
    (entry : Tuple F args) (locals : Locals F past) (outcome : Tuple F out) :
    OrderedRuntime.Structured.readOrigin (newest p past) entry (locals.snoc outcome) = outcome.get p := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact ih locals.2

omit [TypeFormers τ] [Isotope.Subtyping τ] [TypeModel τ] in
theorem read_nextRuntime {F : OrderedRuntime.Structured.Ty τ → Type u}
    (entry : Tuple F args) (locals : Locals F past) (outcome : Tuple F (Threaded out)) :
    OrderedRuntime.Structured.readOrigin (nextRuntime past out) entry (locals.snoc outcome) =
      outcome.get (runtimePort out) :=
  read_newest _ _ _ _

theorem eval_primitive (i : Data ins) (d : Data out) (op : Instruction (Pure τ) (Effect Φ) ins out)
    (inputs : Wires (Threaded args) past ins) (rest : Code Φ a o (nextRuntime past out))
    (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded args))
    (locals : Locals (WireValues (τ := τ) (σ := σ)) past) :
    eval (ε := ε) (Wiring.primitive i d op live inputs rest) entry locals =
      (wireModel (ε := ε) (σ := σ)).primitive (.ordered i d op)
        (Wires.read (withRuntime live inputs) entry locals) >>= fun output =>
      eval (ε := ε) rest entry (locals.snoc output) := by rfl

theorem eval_finish (source : Origin (Threaded args) past (.value B))
    (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded args))
    (locals : Locals (WireValues (τ := τ) (σ := σ)) past) :
    eval (ε := ε) (Wiring.finish (Φ := Φ) (a := a) past live source) entry locals =
      Part.some (point (readWire source entry locals) (readWire live entry locals)) := by
  simp only [eval, Wiring.finish, NestedTheta.Term.denoteOpenWith, read_appended, read_cons]
  rfl

theorem eval_choice (i : Data ins) (d : Data out)
    (left right : Code (past := []) Φ i d (.arg (runtimePort ins)))
    (selector : Origin (Threaded args) past (.control 2))
    (inputs : Wires (Threaded args) past ins) (rest : Code Φ a o (nextRuntime past out))
    (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded args))
    (locals : Locals (WireValues (τ := τ) (σ := σ)) past) :
    eval (ε := ε) (Wiring.choice i d left right selector live inputs rest) entry locals =
      eval (ε := ε) (past := []) (Fin.cases left (fun _ => right) (readWire selector entry locals).down)
        (Wires.read (withRuntime live inputs) entry locals) PUnit.unit >>= fun output =>
      eval (ε := ε) rest entry (locals.snoc output) := by
  simp only [eval, Wiring.choice, NestedTheta.Term.denoteOpenWith, NestedTheta.Node.ofBase,
    gammaNode, read_cons, NestedTheta.Kind.denoteWith]
  rfl

private def selectedPoint (p : (TyDen X ⊕ TyDen Y) × σ) :
    Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (results (Silmaril.coprod X Y))) :=
  OrderedRuntime.Structured.decode (choiceData p.1, p.2)

private theorem call_wire (route : Input S A) (op : TwoBlock.Instruction Φ A B)
    (source : TyDen S) (value : TyDen A) (token : σ) (selected : readRoute route source = some value) :
    (wireModel (ε := ε) (σ := σ)).primitive
        (.ordered (carriedData S) (carriedData B) (.effect (.acyclic (.call route op))))
        (point source token) =
      Part.map (fun p => point p.1 p.2) ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) op value).run token) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := carried B))
    (((match readRoute route source with
      | some v => TwoBlock.call (ε := ε) op v >>= fun b => pure (pack b)
      | none => StateT.mk fun _ => Part.none) : StateT σ Part.{u} _).run token) = _
  rw [selected]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

private theorem classify_wire (route : Input S A) (op : TwoBlock.Instruction Φ A (Silmaril.coprod X Y))
    (source : TyDen S) (value : TyDen A) (token : σ) (selected : readRoute route source = some value) :
    (wireModel (ε := ε) (σ := σ)).primitive
        (.ordered (carriedData S) (resultData _) (.effect (.acyclic (.classify route op))))
        (point source token) =
      Part.map selectedPoint ((callCase (ε := ε) (m := StateT σ Part.{u}) op value).run token) := by
  change Part.map (OrderedRuntime.Structured.decode (ts := results (Silmaril.coprod X Y)))
    (((match readRoute route source with
      | some v => callCase (ε := ε) op v >>= fun b => pure (choiceData b)
      | none => StateT.mk fun _ => Part.none) : StateT σ Part.{u} _).run token) = _
  rw [selected]
  simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some,
    Part.bind_some_eq_map, Part.map_map]
  rfl

/-- The continuation gets the sole state paired with the body result. This law
is open in the current numbered scope and in the output ports. -/
theorem emit_denote (b : Body Φ A B) (route : Input S A)
    (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded args))
    (locals : Locals (WireValues (τ := τ) (σ := σ)) past)
    (live : Origin (Threaded args) past runtime) (source : Origin (Threaded args) past (.value S))
    (x : TyDen A) (selected : readRoute route (readWire source entry locals) = some x)
    (next : Tail Φ a o B) (post : TyDen B × σ → Part (Tuple (WireValues (τ := τ) (σ := σ)) (Threaded outs)))
    (resume : ∀ (future : List (Ports (OrderedRuntime.Structured.Ty τ)))
      (token : Origin (Threaded args) future runtime) (value : Origin (Threaded args) future (.value B))
      (env : Locals (WireValues (τ := τ) (σ := σ)) future),
      eval (ε := ε) (next future token value) entry env =
        post (readWire value entry env, readWire token entry env)) :
    eval (ε := ε) (emit b route live source next) entry locals =
      ((bodyAction (ε := ε) (m := StateT σ Part.{u}) b x).run (readWire live entry locals)).bind post := by
  induction b generalizing args outs past S with
  | instruction op =>
    simp only [emit, eval_primitive]
    rw [read_appended, read_cons]
    change ((wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive _
      (point (readWire source entry locals) (readWire live entry locals)) >>= _) = _
    rw [call_wire _ _ _ _ _ selected]
    simp only [bodyAction, Part.bind_eq_bind, Part.bind_map]
    congr 1
    funext p
    rw [resume, read_newest, read_nextRuntime]
    cases p
    rfl
  | sequence first last ihFirst ihLast =>
    simp only [emit, bodyAction, StateT.run_bind, Part.bind_eq_bind, Part.bind_assoc]
    apply ihFirst _ _ _ _ _ _ selected
    intro future token value env
    exact ihLast .direct entry env token value (readWire value entry env) rfl next post resume
  | @choice A X Y B op left right ihLeft ihRight =>
    simp only [emit, eval_primitive]
    rw [read_appended, read_cons]
    change ((wireModel (Φ := Φ) (ε := ε) (σ := σ)).primitive _
      (point (readWire source entry locals) (readWire live entry locals)) >>= _) = _
    rw [classify_wire _ _ _ _ _ selected]
    simp only [bodyAction, Part.bind_eq_bind, Part.bind_map, StateT.run_bind, Part.bind_assoc]
    congr 1
    funext p
    obtain ⟨branch, token⟩ := p
    rw [eval_choice, read_appended, read_cons]
    have finish_ok {Z : τ} (entry : Tuple (WireValues (τ := τ) (σ := σ)) (Threaded (carried (Silmaril.coprod X Y)))) :
        ∀ (future : List (Ports (OrderedRuntime.Structured.Ty τ)))
          (carry : Origin (Threaded (carried (Silmaril.coprod X Y))) future runtime)
          (value : Origin (Threaded (carried (Silmaril.coprod X Y))) future (.value Z))
          (env : Locals (WireValues (τ := τ) (σ := σ)) future),
          eval (ε := ε) (Wiring.finish (Φ := Φ) (a := carriedData (Silmaril.coprod X Y)) future carry value) entry env =
            (fun (p : TyDen Z × σ) => Part.some (point p.1 p.2)) (readWire value entry env, readWire carry entry env) :=
      fun _ _ _ _ => eval_finish _ _ _
    have keep (output : TyDen B × σ) :
        eval (ε := ε)
          (next _ (nextRuntime (past ++ [Threaded (results (Silmaril.coprod X Y))]) (carried B))
            (newest .head (past ++ [Threaded (results (Silmaril.coprod X Y))])))
          entry ((locals.snoc (selectedPoint (branch, token))).snoc (point output.1 output.2)) =
        post output := by
      rw [resume, read_newest, read_nextRuntime]
      cases output
      rfl
    cases branch with
    | inl leftValue =>
      let payload := (TypeModel.coprodEquiv X Y).symm (Sum.inl leftValue)
      have arm := ihLeft (args := carried (Silmaril.coprod X Y)) (a := carriedData _)
        (outs := carried B) (o := carriedData _) (past := []) .left (point payload token) PUnit.unit
        (.arg (runtimePort (carried (Silmaril.coprod X Y)))) (.arg .head) leftValue
        (show readRoute (.left (X := X) (Y := Y)) payload = some leftValue by
          change ((TypeModel.coprodEquiv X Y) payload).getLeft? = _
          rw [Equiv.apply_symm_apply]; rfl)
        Wiring.finish (fun p => Part.some (point p.1 p.2)) (finish_ok _)
      simp only [read_newest, read_nextRuntime]
      change (eval (ε := ε) (past := []) (emit left (past := []) .left (.arg _) (.arg .head) Wiring.finish)
        (point payload token) PUnit.unit >>= _) = _
      rw [arm]
      simp only [Part.bind_eq_bind, Part.bind_assoc, Part.bind_some]
      congr 1
      funext output
      exact keep output
    | inr rightValue =>
      let payload := (TypeModel.coprodEquiv X Y).symm (Sum.inr rightValue)
      have arm := ihRight (args := carried (Silmaril.coprod X Y)) (a := carriedData _)
        (outs := carried B) (o := carriedData _) (past := []) .right (point payload token) PUnit.unit
        (.arg (runtimePort (carried (Silmaril.coprod X Y)))) (.arg .head) rightValue
        (show readRoute (.right (X := X) (Y := Y)) payload = some rightValue by
          change ((TypeModel.coprodEquiv X Y) payload).getRight? = _
          rw [Equiv.apply_symm_apply]; rfl)
        Wiring.finish (fun p => Part.some (point p.1 p.2)) (finish_ok _)
      simp only [read_newest, read_nextRuntime]
      change (eval (ε := ε) (past := []) (emit right (past := []) .right (.arg _) (.arg .head) Wiring.finish)
        (point payload token) PUnit.unit >>= _) = _
      rw [arm]
      simp only [Part.bind_eq_bind, Part.bind_assoc, Part.bind_some]
      congr 1
      funext output
      exact keep output

theorem body_denote (b : Body Φ A B) (x : TyDen A) (token : σ) :
    eval (ε := ε) (Wiring.body b) (point x token) PUnit.unit =
      Part.map (fun p => point p.1 p.2) ((bodyAction (ε := ε) (m := StateT σ Part.{u}) b x).run token) := by
  rw [← Part.bind_some_eq_map]
  exact emit_denote (past := []) b .direct (point x token) PUnit.unit (.arg _) (.arg .head) x rfl
    Wiring.finish _ (fun _ _ _ _ => eval_finish _ _ _)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Proofs

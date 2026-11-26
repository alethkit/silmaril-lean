module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Association

/-! # The numbered compiler and the right-associated label parser agree -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Proofs

open TwoBlock.TwoExit (Carrier ExitCode Pure)
open OrderedRuntime.Structured (Data Threaded runtime nextRuntime runtimePort Instruction)
open NestedTheta.ExplicitRuntime (Checked)
open ExplicitRuntime.Reverse (BodyView)
open Wires.Reverse (Vertex readBody readBody_lift)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A I B K M C J E D S : τ}

private abbrev labels (b : Body Φ A B) := (BodyView.ofBody b).1

/-- Count the emitted nodes and the two terminating returns of a choice.
The continuation's own budget is counted separately. -/
private def weight : {A B : τ} → Body Φ A B → Nat
  | _, _, .instruction _ => 1
  | _, _, .sequence first last => weight first + weight last
  | _, _, .choice _ left right => 4 + weight left + weight right

private theorem labels_nonempty (b : Body Φ A B) : labels b ≠ [] := by
  induction b with
  | instruction => simp [labels, BodyView.ofBody]
  | choice => simp [labels, BodyView.ofBody]
  | sequence l r first _ =>
    change labels l ++ labels r ≠ []
    simp [first]

variable [DecidableEq τ]

private theorem body_parse {b : Body Φ A B} (canonical : RightAssociated b)
    (fuel : Nat) (enough : weight b ≤ fuel) :
    body fuel A (labels b) = some ⟨B, b⟩ := by
  induction canonical generalizing fuel with
  | instruction op =>
    cases fuel with
    | zero => simp [weight] at enough
    | succ n => simp [labels, BodyView.ofBody, body]
  | @choice A X Y B op l r hl hr ihL ihR =>
    cases fuel with
    | zero => simp [weight] at enough
    | succ n =>
      have hl' : weight l ≤ n := by simp only [weight] at enough; omega
      have hr' : weight r ≤ n := by simp only [weight] at enough; omega
      simp [labels, BodyView.ofBody, body, ihL _ hl', ihR _ hr']
  | @thenInstruction A X B op rest ht ih =>
    cases fuel with
    | zero => simp [weight] at enough
    | succ n =>
      have hrest : weight rest ≤ n := by simp only [weight] at enough; omega
      have parsed := ih n hrest
      cases h : labels rest with
      | nil => exact (labels_nonempty rest h).elim
      | cons hd tail =>
        rw [h] at parsed
        simp [labels, BodyView.ofBody, body, h, parsed]
  | @thenChoice A X Y K B op l r rest hl hr ht ihL ihR ihT =>
    cases fuel with
    | zero => simp [weight] at enough
    | succ n =>
      have hl' : weight l ≤ n := by simp only [weight] at enough; omega
      have hr' : weight r ≤ n := by simp only [weight] at enough; omega
      have ht' : weight rest ≤ n := by simp only [weight] at enough; omega
      have parsed := ihT n ht'
      cases h : labels rest with
      | nil => exact (labels_nonempty rest h).elim
      | cons hd tail =>
        rw [h] at parsed
        simp [labels, BodyView.ofBody, body, h, parsed, ihL _ hl', ihR _ hr']

omit [DecidableEq τ] in
private theorem budget_lift {args outs : Ports (OrderedRuntime.Structured.Ty τ)} {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
    {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : NestedTheta.Term (ExplicitRuntime.Op Φ) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked (Pure τ) (ExplicitRuntime.Effect Φ) a b live t) :
    budget (Wires.liftChecked checked).1 = budget t := by
  induction checked with
  | ret => rfl
  | primitive live i o op wires rest ih =>
    simp only [Wires.liftChecked, budget, NestedTheta.Node.ofBase, OrderedRuntime.Structured.primitiveNode, ih]
    rfl
  | gamma extra selector live i o wires sigs arms rest ihArms ihRest =>
    simp only [Wires.liftChecked, budget, ihArms, ihRest]
    rfl
  | theta live i wires sigs b rest ihArms ihRest =>
    simp only [Wires.liftChecked, budget, ihArms, ihRest]
    rfl

section Budget
open ExplicitRuntime.Wiring (Code Tail emit)

variable {args ins out outs : Ports (OrderedRuntime.Structured.Ty τ)} {past : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}

omit [DecidableEq τ] in
private theorem budget_primitive (i : Data ins) (o : Data out)
    (op : Instruction (Pure τ) (ExplicitRuntime.Effect Φ) ins out)
    (inputs : Wires (Threaded args) past ins) (rest : Code Φ a b (nextRuntime past out)) :
    budget (ExplicitRuntime.Wiring.primitive i o op live inputs rest).2.1 = 1 + budget rest.2.1 := rfl

omit [DecidableEq τ] in
private theorem budget_choice (i : Data ins) (o : Data out)
    (l r : Code (past := []) Φ i o (.arg (runtimePort ins)))
    (selector : Origin (Threaded args) past (.control 2))
    (inputs : Wires (Threaded args) past ins) (rest : Code Φ a b (nextRuntime past out)) :
    budget (ExplicitRuntime.Wiring.choice i o l r selector live inputs rest).2.1 =
      1 + (budget l.2.1 + budget r.2.1) + budget rest.2.1 := rfl

omit [DecidableEq τ] in
private theorem budget_emit (program : Body Φ A B) (route : Input S A)
    (source : Origin (Threaded args) past (.value S)) (next : Tail Φ a b B) (tailCost : Nat)
    (continuation : ∀ future token value, budget (next future token value).2.1 = tailCost) :
    budget (emit program route live source next).2.1 = weight program + tailCost := by
  induction program generalizing args outs past S tailCost with
  | instruction op =>
    simp only [emit, budget_primitive, weight, continuation]
  | sequence first last ihL ihR =>
    simp only [emit, weight]
    rw [ihL _ _ _ (weight last + tailCost) (fun _ _ _ => ihR _ _ _ _ continuation)]
    rw [Nat.add_assoc]
  | choice op l r ihL ihR =>
    simp only [emit, budget_primitive, budget_choice, weight, continuation]
    rw [ihL _ _ _ 1 (fun _ _ _ => rfl), ihR _ _ _ 1 (fun _ _ _ => rfl)]
    omega

omit [DecidableEq τ] in
private theorem budget_thetaBody (s : Loop Φ A B K E D) :
    budget (ExplicitRuntime.Wiring.thetaBody s).2.1 = weight s.body + 7 := by
  simp only [ExplicitRuntime.Wiring.thetaBody, budget_primitive, budget_choice, ExplicitRuntime.Wiring.bodyArm]
  rw [budget_emit _ _ _ _ 2 (fun _ _ _ => rfl)]
  change 1 + (1 + (2 + (weight s.body + 2)) + 1) = _
  omega

end Budget

private def loopLabels (s : Loop Φ A B K E D) : List (Vertex (τ := τ) (Φ := Φ)) :=
  [.theta [.header s.header, .gamma [[.headerExit], labels s.body ++ [.join s.join]]]]

omit [DecidableEq τ] in
private theorem read_thetaBody (s : Loop Φ A B K E D) :
    ExplicitRuntime.Reverse.read (ExplicitRuntime.Wiring.thetaBody s).2.1 =
      [.header s.header, .gamma [[.headerExit], labels s.body ++ [.join s.join]]] := by
  have h := ExplicitRuntime.Reverse.read_compiled s
  rw [ExplicitRuntime.graph, NestedTheta.Term.toTerm_toGraph] at h
  change [ExplicitRuntime.Reverse.Vertex.theta (ExplicitRuntime.Reverse.read
    (ExplicitRuntime.Wiring.thetaBody s).2.1)] = _ at h
  exact ExplicitRuntime.Reverse.Vertex.theta.inj (List.cons.inj h).1

omit [DecidableEq τ] in
private theorem cut_compile (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D) :
    cut (compile p q) =
      some ([.classifier (X := ExitCode M M) (Y := I) p.gate, .gamma [[], loopLabels p.loop]],
        loopLabels q) := by
  simp only [cut, compile, join, NestedTheta.Term.toTerm_toGraph]
  change (do
    let choice ← ExplicitRuntime.Reverse.Vertex.gamma <$> ([some [], (do
      let tag ← ExplicitRuntime.Reverse.Vertex.theta <$> readBody
        (Wires.liftChecked (ExplicitRuntime.Wiring.thetaBody p.loop).2.2).1
      pure [tag])] : List (Option (List (Vertex (τ := τ) (Φ := Φ))))).mapM id
    let last ← ExplicitRuntime.Reverse.Vertex.theta <$> readBody
      (Wires.liftChecked (ExplicitRuntime.Wiring.thetaBody q).2.2).1
    pure ([ExplicitRuntime.Reverse.Vertex.classifier (X := ExitCode M M) (Y := I) p.gate, choice], [last])) = _
  rw [readBody_lift (ExplicitRuntime.Wiring.thetaBody p.loop).2.2,
    readBody_lift (ExplicitRuntime.Wiring.thetaBody q).2.2,
    read_thetaBody, read_thetaBody]
  rfl

omit [DecidableEq τ] in
-- The other 22 units are wrapper vertices and region returns outside the two bodies.
private theorem budget_compile (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D) :
    budget (compile p q).toTerm = 22 + weight p.loop.body + weight q.body := by
  rw [compile, join, NestedTheta.Term.toTerm_toGraph]
  change 1 + (1 + (1 + (1 + budget (Wires.liftChecked
      (ExplicitRuntime.Wiring.thetaBody p.loop).2.2).1 + 1)) +
    (1 + (1 + budget (Wires.liftChecked (ExplicitRuntime.Wiring.thetaBody q).2.2).1 + 1))) = _
  rw [budget_lift, budget_lift, budget_thetaBody, budget_thetaBody]
  omega

private theorem loop_parse (s : Loop Φ A B K E D) (h : RightAssociated s.body) (fuel : Nat)
    (enough : weight s.body ≤ fuel) :
    loop fuel A E D (loopLabels s) = some ⟨B, K, s⟩ := by
  simp [loopLabels, loop, body_parse h fuel enough]

theorem parse_thetaBody (s : Loop Φ A B K E D) (h : RightAssociated s.body) :
    loop (budget (Wires.liftChecked (ExplicitRuntime.Wiring.thetaBody s).2.2).1)
      A E D [.theta (ExplicitRuntime.Reverse.read (ExplicitRuntime.Wiring.thetaBody s).2.1)] =
      some ⟨B, K, s⟩ := by
  rw [budget_lift, budget_thetaBody, read_thetaBody]
  exact loop_parse s h _ (by omega)

private theorem guarded_parse (s : Conditional.Guarded Φ A I B K M M) (h : RightAssociated s.loop.body)
    (fuel : Nat) (enough : weight s.loop.body ≤ fuel) :
    guarded fuel A I M
      [.classifier (X := ExitCode M M) (Y := I) s.gate, .gamma [[], loopLabels s.loop]] =
      some ⟨B, K, s⟩ := by
  simp [guarded, loop_parse s.loop h fuel enough]

variable [DecidableEq Φ]

theorem recognize_rightAssociated (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D)
    (hp : RightAssociated p.loop.body) (hq : RightAssociated q.body) :
    recognize (compile p q) = some ⟨⟨B, K, C, J, p, q⟩, rfl⟩ := by
  let c : Components Φ A I M E D := ⟨B, K, C, J, p, q⟩
  have parsed : candidate (compile p q) = some c := by
    let n := 22 + weight p.loop.body + weight q.body
    have first := guarded_parse p hp n (by dsimp [n]; omega)
    have second := loop_parse q hq n (by dsimp [n]; omega)
    simp only [candidate, cut_compile, budget_compile]
    change (do
      let ⟨b, k, p'⟩ ← guarded n A I M
        [.classifier (X := ExitCode M M) (Y := I) p.gate, .gamma [[], loopLabels p.loop]]
      let ⟨d, j, q'⟩ ← loop n M E D (loopLabels q)
      pure (⟨b, k, d, j, p', q'⟩ : Components Φ A I M E D)) = some c
    rw [first, second]
    rfl
  exact complete c parsed rfl

theorem complete_generated (p : Conditional.Guarded Φ A I B K M M) (q : Loop Φ M C J E D) :
    (recognize (compile p q)).isSome = true := by
  obtain ⟨p', q', hp, hq, graph⟩ := compile_associated p q
  rw [← graph, recognize_rightAssociated p' q' hp hq]
  rfl

theorem recognize_isSome_iff (g : Graph Φ A I M E D) :
    (recognize g).isSome = true ↔ ∃ c : Components Φ A I M E D, c.graph = g := by
  constructor
  · cases recognize g with
    | none => simp
    | some m => exact fun _ => ⟨m.components, m.wiring⟩
  · rintro ⟨c, rfl⟩
    exact complete_generated c.first c.second

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Proofs

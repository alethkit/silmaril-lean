module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Places

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before middle after vars outs all : List (Ty Data)} {t : Ty Data}

abbrev PortsPred (nodes : List (Ty Data)) := ∀ {t}, Port nodes t → Prop

@[expose] def PortsSatisfy (pred : PortsPred before) (refs : Tuple (Port before) vars) : Prop :=
  ∀ t (slot : Port vars t), pred (refs.get slot)

theorem satisfyNil (pred : PortsPred before) : PortsSatisfy pred (.nil : Tuple (Port before) []) :=
  fun _ r => nomatch r

theorem satisfyCons {pred : PortsPred before} {p : Port before t} {ps : Tuple (Port before) vars}
    (first : pred p) (rest : PortsSatisfy pred ps) : PortsSatisfy pred (.cons p ps) := by
  intro t r
  cases r with
  | head => exact first
  | tail r => exact rest _ r

theorem satisfyMap {pred : PortsPred before} {mapped : PortsPred after}
    (f : Embed before after) {refs : Tuple (Port before) vars}
    (h : PortsSatisfy pred refs) (step : ∀ t (r : Port before t), pred r → mapped (f r)) :
    PortsSatisfy mapped (refs.map fun _ r => f r) := by
  intro t slot
  rw [Simple.Proofs.get_map]
  exact step _ _ (h t slot)

@[expose] def available (allow : PortsPred before) :
    {after : List (Ty Data)} → Simple.Code P params before after → PortsPred after
  | _, .empty => allow
  | _, .emit prior _ _ => portConsCases True (available allow prior)

@[expose] def checks (allow : PortsPred before) :
    {after : List (Ty Data)} → Simple.Code P params before after → Prop
  | _, .empty => True
  | _, .emit prior _ args => checks allow prior ∧ PortsSatisfy (available allow prior) args

theorem availableLift (code : Simple.Code P params before after) {allow : PortsPred before}
    {p : Port before t} (h : allow p) : available allow code (code.lift p) := by
  induction code with
  | empty => exact h
  | emit prior label args ih => exact ih

private theorem appendAvailable (a : Simple.Code P params before middle)
    (b : Simple.Code P params middle after) (allow : PortsPred before) (r : Port after t) :
    available allow (a.append b) r ↔ available (available allow a) b r := by
  induction b with
  | empty => rfl
  | emit prior _ _ ih =>
    cases r with
    | head => rfl
    | tail r => exact ih r

theorem appendChecks (a : Simple.Code P params before middle)
    (b : Simple.Code P params middle after) {allow : PortsPred before}
    (left : checks allow a) (right : checks (available allow a) b) :
    checks allow (a.append b) := by
  induction b with
  | empty => exact left
  | emit prior label args ih =>
    refine ⟨ih right.1, fun t r => ?_⟩
    exact (appendAvailable a prior allow _).mpr (right.2 t r)

private theorem appendOutputs (a : Simple.Code P params before middle)
    (b : Simple.Code P params middle after) {allow : PortsPred before}
    {refs : Tuple (Port after) vars} (right : PortsSatisfy (available (available allow a) b) refs) :
    PortsSatisfy (available allow (a.append b)) refs :=
  fun _ r => (appendAvailable a b allow _).mpr (right _ r)

@[expose] def StraightBuildChecks (allow : PortsPred before) (b : Simple.Build P params before vars) : Prop :=
  checks allow b.code ∧ PortsSatisfy (available allow b.code) b.refs

theorem exprChecks (params : List (Ty Data)) (e : Expr P vars t)
    (ctx : Tuple (Port before) vars) {allow : PortsPred before}
    (entry : PortsSatisfy allow ctx) :
    StraightBuildChecks allow (e.lower (params := params) ctx) := by
  refine Expr.rec
    (motive_1 := fun _ expr => ∀ (nodes : List (Ty Data)) (ctx : Tuple (Port nodes) vars)
      (allow : PortsPred nodes), PortsSatisfy allow ctx →
        StraightBuildChecks allow (expr.lower (params := params) ctx))
    (motive_2 := fun _ args => ∀ (nodes : List (Ty Data)) (ctx : Tuple (Port nodes) vars)
      (allow : PortsPred nodes), PortsSatisfy allow ctx →
        StraightBuildChecks allow (args.lower (params := params) ctx))
    ?_ ?_ ?_ ?_ e before ctx allow entry
  · intro t slot nodes ctx allow entry
    exact ⟨trivial, satisfyCons (entry _ slot) (satisfyNil allow)⟩
  · intro ins t instr args ih nodes ctx allow entry
    exact ⟨ih nodes ctx allow entry, satisfyCons trivial (satisfyNil _)⟩
  · intro nodes ctx allow entry
    exact ⟨trivial, satisfyNil allow⟩
  · intro t ts first rest ihFirst ihRest nodes ctx allow entry
    let head := first.lower (params := params) ctx
    let tail := rest.lower (params := params) (head.code.liftRefs ctx)
    have left : StraightBuildChecks allow head := ihFirst nodes ctx allow entry
    have mid := satisfyMap (fun r => head.code.lift r) entry (fun _ _ => availableLift head.code)
    have right : StraightBuildChecks (available allow head.code) tail :=
      ihRest head.nodes (head.code.liftRefs ctx) (available allow head.code) mid
    refine ⟨appendChecks head.code tail.code left.1 right.1, ?_⟩
    apply appendOutputs head.code tail.code
    exact satisfyCons (availableLift tail.code (left.2 _ .head)) right.2

theorem phiChecks (cond : Port before .bool) (yes no : Tuple (Port before) outs)
    {allow : PortsPred before} (condition : allow cond)
    (left : PortsSatisfy allow yes) (right : PortsSatisfy allow no) :
    StraightBuildChecks allow (phiNodes (P := P) (params := params) cond yes no) := by
  induction yes with
  | nil =>
    cases no
    exact ⟨trivial, satisfyNil allow⟩
  | cons y ys ih =>
    cases no with
    | cons n ns =>
      let tail := phiNodes (P := P) (params := params) cond ys ns
      have rest : StraightBuildChecks allow tail :=
        ih ns (fun _ r => left _ (.tail r)) (fun _ r => right _ (.tail r))
      refine ⟨⟨rest.1, ?_⟩, ?_⟩
      · exact satisfyCons (availableLift tail.code condition)
          (satisfyCons (availableLift tail.code (left _ .head))
            (satisfyCons (availableLift tail.code (right _ .head)) (satisfyNil _)))
      · apply satisfyCons True.intro
        exact satisfyMap Port.tail rest.2 (fun _ _ h => h)

theorem paramChecks (slots : Tuple (Port params) outs) (allow : PortsPred before) :
    StraightBuildChecks allow (paramNodes (P := P) (nodes := before) slots) := by
  induction slots with
  | nil => exact ⟨trivial, satisfyNil allow⟩
  | cons input rest ih =>
    refine ⟨⟨ih.1, satisfyNil _⟩, ?_⟩
    apply satisfyCons True.intro
    exact satisfyMap Port.tail ih.2 (fun _ _ h => h)

end Silmaril.SSA.PEG.Simple.Structured.Proofs

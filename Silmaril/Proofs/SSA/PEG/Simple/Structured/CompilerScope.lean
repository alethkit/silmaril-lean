module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.LoopAccess

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before middle after vars outs all : List (Ty Data)} {t : Ty Data}
variable {catalog active : List (Region all.length)}

private theorem seqCertified {a : Code P params before middle} {b : Code P params middle after}
    (p : Place catalog active (.seq a b))
    {left : Tuple (Port middle) vars} {right : Tuple (Port after) outs}
    (first : Certified p.left left) (second : Certified p.right right) :
    Certified p right := by
  exact ⟨second.1, fun holes seed => second.2 _ (first.2 holes seed)⟩

private theorem exprCertified (e : Expr P vars t) (ctx : Tuple (Port before) vars)
    (p : Place catalog active (expr (params := params) e ctx).code) (entry : Entry p ctx) :
    Certified p (expr (params := params) e ctx).refs :=
  straightBuildGood (e.lower ctx) p (exprChecks params e ctx entry)

private def LowerSafe (neg : P [.bool] .bool) (stmt : Stmt P true vars outs) : Prop :=
  ∀ {before : List (Ty Data)} (ctx : Tuple (Port before) vars)
    {active : List (Region all.length)} (p : Place catalog active (lower (params := params) neg stmt ctx).code),
    Entry p ctx → Certified p (lower (params := params) neg stmt ctx).refs

private theorem lowerSafe (neg : P [.bool] .bool) (stmt : Stmt P true vars outs) :
    LowerSafe (params := params) (catalog := catalog) neg stmt := by
  induction stmt with
  | assign e =>
    intro before ctx active p entry
    have eOK := exprCertified e ctx p entry
    exact ⟨satisfyCons (eOK.1 _ .head) (exitLift p entry), eOK.2⟩
  | project slots =>
    intro before ctx active p entry
    refine ⟨?_, fun _ h => h⟩
    intro t r
    change Visible _ _ (pos (p.embed ((select ctx slots).get r)))
    rw [Simple.Proofs.get_select]
    exact entry _ (slots.get r)
  | seq a b ihA ihB =>
    intro before ctx active p entry
    let left := lower (params := params) neg a ctx
    let right := lower (params := params) neg b left.refs
    change Place catalog active (.seq left.code right.code) at p
    have first := ihA ctx p.left entry
    exact seqCertified p first (ihB left.refs p.right first.1)
  | branch test yes no ihYes ihNo =>
    intro before ctx active p entry
    let c := expr (params := params) test ctx
    let cRefs := c.code.liftRefs ctx
    let y := lower (params := params) neg yes cRefs
    let n := lower (params := params) neg no (y.code.liftRefs cRefs)
    let flag := n.code.lift (y.code.lift (c.refs.get .head))
    let join := phiNodes (P := P) (params := params) flag (n.code.liftRefs y.refs) n.refs
    change Place catalog active (.seq c.code (.seq y.code (.seq n.code (.straight join.code)))) at p
    have guard := exprCertified test ctx p.left entry
    have yEntry := exitLift p.left entry
    have yOK := ihYes cRefs p.right.left yEntry
    have nEntry := exitLift p.right.left yEntry
    have nOK := ihNo (y.code.liftRefs cRefs) p.right.right.left nEntry
    have yesArm := exitLift p.right.right.left yOK.1
    have joinOK := straightBuildGood join p.right.right.right
      (phiChecks flag (n.code.liftRefs y.refs) n.refs (guard.1 _ .head) yesArm nOK.1)
    exact seqCertified p guard (seqCertified p.right yOK (seqCertified p.right.right nOK joinOK))
  | @«while» carried _ test stmt ih =>
    intro before ctx active p entry
    let slots := (ports carried).map (fun _ r => portLeft (right := before) r)
    let c := expr (params := params) test slots
    let b := lower (params := params) neg stmt (c.code.liftRefs slots)
    change Place catalog active (.loop ctx (.seq c.code b.code) (b.code.lift (c.refs.get .head)) b.refs neg) at p
    have cEntry := thetaEntry p
    have cOK := exprCertified test slots p.inner.left cEntry
    have bOK := ih (c.code.liftRefs slots) p.inner.right (exitLift p.inner.left cEntry)
    exact loopCertified p entry (cOK.1 _ .head) (seqCertified p.inner cOK bOK)

theorem programGood (p : Program P true params t) (neg : P [.bool] .bool) :
    let code := (program p neg).code
    GoodRows (regions code (fun r => r) 0 none) (fun r => r) (code.rows (fun r => nomatch r) (fun r => r) none) := by
  let init := Build.straight (paramNodes (P := P) (nodes := []) (ports params))
  let body := lower (params := params) neg p.body init.refs
  let code := Code.seq init.code body.code
  let root := Place.root code
  have initial := straightBuildGood (paramNodes (P := P) (nodes := []) (ports params)) root.left (paramChecks _ _)
  have bodyOK := lowerSafe neg p.body init.refs root.right initial.1
  have checked := seqCertified root initial bodyOK
  exact checked.2 (fun r => nomatch r) (fun _ r => nomatch r)

end Silmaril.SSA.PEG.Simple.Structured.Proofs

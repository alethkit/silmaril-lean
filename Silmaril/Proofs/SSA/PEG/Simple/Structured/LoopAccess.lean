module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Access

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before vars inside all : List (Ty Data)} {t : Ty Data}
variable {catalog active : List (Region all.length)}
variable {init : Tuple (Port before) vars} {body : Code P params (vars ++ before) inside}
variable {guard : Port inside .bool} {next : Tuple (Port inside) vars} {neg : P [.bool] .bool}
variable (p : Place catalog active (.loop init body guard next neg))

private theorem insideOffset : p.inner.offset = p.offset + vars.length + 2 := rfl

private theorem finalOffset :
    p.own.stop = p.offset + (vars.length + 2 + width body + vars.length) :=
  p.stopPosition

private theorem outsideShell {a : Nat} (lo : p.offset ≤ a) (before : a ≤ p.own.pass.val) :
    AtRegions catalog active a := by
  have cut := p.passPosition
  have stop := finalOffset p
  have off := insideOffset p
  intro f mem
  refine (p.shell lo (by omega) (.inl (by omega)) f mem).trans ?_
  exact ⟨fun h => h.elim (fun both => (Nat.not_lt_of_ge before both.2.1).elim) id, .inr⟩

private theorem insideShell {a : Nat} (inLoop : p.own.Contains a)
    (noBody : a < p.inner.offset ∨ p.inner.offset + width body ≤ a) :
    AtRegions catalog (p.own :: active) a := by
  have cut := p.passPosition
  have lo := inLoop.1
  intro f mem
  refine (p.shell (by omega) inLoop.2 noBody f mem).trans ?_
  rw [List.mem_cons]
  exact or_congr ⟨And.left, fun h => ⟨h, inLoop⟩⟩ Iff.rfl

theorem passSite : AtRegions catalog active p.own.pass.val := by
  apply outsideShell p _ (Nat.le_refl _)
  rw [p.passPosition]
  exact Nat.le_add_right _ _

theorem exitSite (r : Port vars t) : AtRegions catalog active (pos (p.embed (portLeft r))) := by
  apply outsideShell p
  · rw [p.address]
    exact Nat.le_add_right _ _
  · rw [p.address, p.passPosition, posLeft]
    have bound : pos r < vars.length := (numberPort r).id.isLt
    omega

theorem negSite : AtRegions catalog (p.own :: active) (pos (p.embed (negRef vars))) := by
  have address : pos (p.embed (negRef vars)) = p.offset + (vars.length + 1) := by rw [p.address, posNeg]
  have cut := p.passPosition
  have stop := finalOffset p
  have off := insideOffset p
  exact insideShell p ⟨by omega, by omega⟩ (.inl (by omega))

theorem thetaSite (r : Port vars t) :
    AtRegions catalog (p.own :: active) (pos (p.inner.embed (body.lift (portLeft r)))) := by
  have address : pos (p.inner.embed (body.lift (portLeft r))) =
      p.inner.offset + (width body + pos r) := by
    rw [p.inner.address, liftPosition, posLeft]
  have cut := p.passPosition
  have stop := finalOffset p
  have off := insideOffset p
  have bound : pos r < vars.length := (numberPort r).id.isLt
  rw [address, off]
  exact insideShell p ⟨by omega, by omega⟩ (.inr (by omega))

private theorem sourceOrigin {a : Nat} (site : AtRegions catalog active a) :
    ∃ f ∈ catalog, f.pass = p.own.pass ∧
      ∀ outer ∈ catalog, outer.Contains a → outer.pass = p.own.pass ∨ outer.Contains p.own.pass.val :=
  ⟨p.own, p.ownMem, rfl, fun f mem h => .inr ((passSite p f mem).mpr ((site f mem).mp h))⟩

private theorem thetaOrigin {a : Nat} (site : AtRegions catalog (p.own :: active) a) :
    ∃ f ∈ catalog, f.pass = p.own.pass ∧
      ∀ outer ∈ catalog, outer.Contains a → outer.pass = p.own.pass ∨ outer.Contains p.own.pass.val := by
  refine ⟨p.own, p.ownMem, rfl, fun f mem h => ?_⟩
  rcases List.mem_cons.mp ((site f mem).mp h) with rfl | outer
  · exact .inl rfl
  · exact .inr ((passSite p f mem).mpr outer)

private theorem sampleScope {a b : Nat}
    (source : AtRegions catalog active a) (target : AtRegions catalog (p.own :: active) b)
    (f : Region all.length) (mem : f ∈ catalog) (inside : f.Contains b) :
    f.Contains a ∨ EdgeKind.sample p.own.pass = .sample f.pass := by
  rcases List.mem_cons.mp ((target f mem).mp inside) with rfl | scope
  · exact .inr rfl
  · exact .inl ((source f mem).mpr scope)

private theorem thetaGood (r : Port vars t) (initOK : Entry p init) (nextOK : Exit p.inner next) :
    GoodRow (P := P) (params := params) catalog
      ⟨_, .theta p.own.pass,
        .cons (p.inner.embed (body.lift (portRight vars (init.get r))))
          (.cons (p.inner.embed (next.get r)) .nil), none⟩
      (pos (p.inner.embed (body.lift (portLeft r)))) := by
  have site := thetaSite p r
  constructor
  · intro slot
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun j => j.elim0) k) slot
    · intro f mem h
      exact .inl ((site f mem).mpr (List.mem_cons_of_mem _ (initOK _ r f mem h)))
    · intro f mem h
      exact .inl ((site f mem).mpr (nextOK _ r f mem h))
  · intro l h
    cases h
    exact thetaOrigin p site
  · intro l h
    cases h
    exact ⟨p.own, p.ownMem, rfl, (site _ p.ownMem).mpr (.head _)⟩
  · intro slot
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun j => j.elim0) k) slot <;>
      intro l h <;> cases h

private theorem exitGood (r : Port vars t) :
    GoodRow (P := P) (params := params) catalog
      ⟨_, .eval p.own.pass, .cons (p.inner.embed (body.lift (portLeft r)))
          (.cons (p.embed (passRef vars)) .nil), none⟩ (pos (p.embed (portLeft r))) := by
  have site := exitSite p r
  constructor
  · intro slot
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun j => j.elim0) k) slot
    · exact sampleScope p site (thetaSite p r)
    · intro f mem h
      exact .inl ((site f mem).mpr ((passSite p f mem).mp h))
  · intro l h
    cases h
    exact sourceOrigin p site
  · intro l h
    cases h
  · intro slot
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun j => j.elim0) k) slot
    · intro l h
      cases h
    · intro l h
      cases h
      rfl

private theorem passGood :
    GoodRow (P := P) (params := params) catalog ⟨_, .pass p.own.pass, .cons (p.embed (negRef vars)) .nil, top active⟩
      (pos (p.embed (passRef vars))) := by
  constructor
  · intro slot
    exact Fin.cases (sampleScope p (passSite p) (negSite p)) (fun j => j.elim0) slot
  · intro l h
    cases h
    exact sourceOrigin p (passSite p)
  · intro l h
    cases h
  · intro slot
    refine Fin.cases ?_ (fun j => j.elim0) slot
    intro l h
    cases h

private theorem negGood (guardOK : Visible catalog (p.own :: active) (pos (p.inner.embed guard))) :
    GoodRow (P := P) (params := params) catalog ⟨_, .op neg, .cons (p.inner.embed guard) .nil, none⟩
      (pos (p.embed (negRef vars))) :=
  ordinaryRow (.op neg) _ _ (negSite p) (satisfyCons guardOK (satisfyNil _))

theorem thetaEntry :
    Entry p.inner ((ports vars).map fun _ r => portLeft r) := by
  intro t r
  rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
  exact (thetaSite p r).visible

theorem loopCertified (initOK : Entry p init)
    (guardOK : Visible catalog (p.own :: active) (pos (p.inner.embed guard)))
    (bodyOK : Certified p.inner next) :
    Certified p ((ports vars).map fun _ r => portLeft r) := by
  constructor
  · intro t r
    rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
    exact (exitSite p r).visible
  · intro holes oldRows t r
    let innerHoles : Rows P params (vars ++ before) all := loopHoles body init next holes p.embed
    have seed : GoodRows catalog (fun r => p.inner.embed (body.lift r)) innerHoles := by
      intro t r
      rcases WhileProofs.splitCases vars r with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · change GoodRow (P := P) (params := params) catalog (loopHoles body init next holes p.embed (portLeft r)) _
        rw [loopHoles_left]
        exact thetaGood p r initOK bodyOK.1
      · change GoodRow (P := P) (params := params) catalog (loopHoles body init next holes p.embed (portRight vars r)) _
        rw [loopHoles_right]
        exact oldRows _ r
    let innerRows : Rows P params inside all := body.rows innerHoles p.inner.embed (some p.own.pass)
    have innerGood := bodyOK.2 innerHoles seed
    change GoodRow (P := P) (params := params) catalog (loopRows body guard neg (top active) p.embed innerRows r) _
    rcases WhileProofs.splitCases vars r with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · rw [loopRows_exit]
      exact exitGood p r
    · cases r with
      | head =>
        change GoodRow (P := P) (params := params) catalog (loopRows body guard neg (top active) p.embed innerRows (passRef vars)) _
        rw [loopRows_pass]
        exact passGood p
      | tail r =>
        cases r with
        | head =>
          change GoodRow (P := P) (params := params) catalog (loopRows body guard neg (top active) p.embed innerRows (negRef vars)) _
          rw [loopRows_neg]
          exact negGood p guardOK
        | tail r =>
          change GoodRow (P := P) (params := params) catalog (loopRows body guard neg (top active) p.embed innerRows (insideRef vars r)) _
          rw [loopRows_inside]
          exact innerGood _ r

end Silmaril.SSA.PEG.Simple.Structured.Proofs

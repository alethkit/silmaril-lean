module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Visibility

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before after vars ins all : List (Ty Data)} {t : Ty Data}

/-- An edge can add only the region it samples. Loop labels have an
actual region origin, with ancestors determined at its pass address. -/
structure GoodRow (catalog : List (Region all.length)) (row : Row P params all t) (a : Nat) : Prop where
  edge : ∀ slot : Fin row.inputs.length, ∀ f ∈ catalog,
    f.Contains (pos (row.refs.get (portAt row.inputs slot))) →
    f.Contains a ∨ row.label.kind slot = .sample f.pass
  origin : ∀ l, row.label.loop = some l →
    ∃ f ∈ catalog, f.pass = l ∧
      ∀ outer ∈ catalog, outer.Contains a → outer.pass = l ∨ outer.Contains l.val
  theta : ∀ l, row.label.thetaLoop = some l → ∃ f ∈ catalog, f.pass = l ∧ f.Contains a
  index : ∀ slot : Fin row.inputs.length, ∀ l, row.label.kind slot = .index l →
    pos (row.refs.get (portAt row.inputs slot)) = l.val

@[expose] def GoodRows (catalog : List (Region all.length)) (embed : Embed after all)
    (rows : Rows P params after all) : Prop :=
  ∀ t (r : Port after t), GoodRow catalog (rows r) (pos (embed r))

variable {catalog active : List (Region all.length)}

theorem ordinaryRow (label : Label P params (Fin 0) ins t)
    (refs : Tuple (Port all) ins) (a : Nat) (site : AtRegions catalog active a)
    (visible : PortsSatisfy (fun r => Visible catalog active (pos r)) refs) :
    GoodRow catalog ⟨_, label.map (fun op => op) Fin.elim0, refs, none⟩ a := by
  have entry (k : Fin ins.length) (f : Region all.length) (mem : f ∈ catalog)
      (inside : f.Contains (pos (refs.get (portAt ins k)))) : f.Contains a :=
    (site f mem).mpr (visible _ (portAt ins k) f mem inside)
  cases label with
  | param | op | phi =>
    exact ⟨fun k f mem h => .inl (entry k f mem h),
      (fun l h => by cases h), (fun l h => by cases h), (fun k l h => by cases h)⟩
  | theta impossible | pass impossible | eval impossible => exact impossible.elim0

theorem straightGood (code : Simple.Code P params before after)
    (p : Place catalog active (.straight code)) (allow : PortsPred before)
    (entry : ∀ t (r : Port before t), allow r → Visible catalog active (pos (p.embed (code.lift r))))
    (safe : checks allow code) :
    (∀ t (r : Port after t), available allow code r → Visible catalog active (pos (p.embed r))) ∧
      (∀ holes : Rows P params before all, GoodRows catalog (fun r => p.embed (code.lift r)) holes →
        GoodRows catalog p.embed (straightRows holes code p.embed)) := by
  induction code with
  | empty => exact ⟨entry, fun _ h => h⟩
  | emit prior label args ih =>
    let earlier : Place catalog active (.straight prior) :=
      { embed := fun r => p.embed (.tail r)
        offset := p.offset + 1
        address := by
          intro t r
          rw [p.address, posTail]
          omega
        localMem := fun _ h => nomatch h
        activeEarlier := fun f mem => ⟨(p.activeEarlier f mem).1, by have := (p.activeEarlier f mem).2; omega⟩
        external := by
          intro addr lo hi f mem _
          change addr < p.offset + 1 + straightWidth prior at hi
          apply p.external addr (by omega) _ f mem (fun bad => nomatch bad)
          change addr < p.offset + (straightWidth prior + 1)
          omega }
    have past := ih earlier entry safe.1
    have atHead : AtRegions catalog active (pos (p.embed .head)) := by
      apply p.exactAt
      · rw [p.address]
        exact Nat.le_add_right _ _
      · rw [p.address]
        change p.offset + 0 < p.offset + (straightWidth prior + 1)
        omega
      · exact fun _ h => nomatch h
    constructor
    · intro t r available
      cases r with
      | head => exact atHead.visible
      | tail r => exact past.1 _ r available
    · intro holes oldRows t r
      cases r with
      | head =>
        exact ordinaryRow label _ _ atHead
          (satisfyMap (fun r => p.embed (.tail r)) safe.2 past.1)
      | tail r => exact past.2 holes oldRows _ r

/-- A statement extension sees only references allowed by the active
regions, both before it runs and in its exported exit context. -/
@[expose] def Entry {code : Code P params before after} (p : Place catalog active code)
    (ctx : Tuple (Port before) vars) : Prop :=
  PortsSatisfy (fun r => Visible catalog active (pos (p.embed (code.lift r)))) ctx

@[expose] def Exit {code : Code P params before after} (p : Place catalog active code)
    (refs : Tuple (Port after) vars) : Prop :=
  PortsSatisfy (fun r => Visible catalog active (pos (p.embed r))) refs

theorem exitLift {code : Code P params before after} (p : Place catalog active code)
    {ctx : Tuple (Port before) vars} (entry : Entry p ctx) :
    Exit p (code.liftRefs ctx) :=
  satisfyMap (fun r => code.lift r) entry (fun _ _ h => h)

/-- Exit visibility is independent of the row proof. In a loop, it supplies
the permission for the feedback operands before the body rows are checked. -/
@[expose] def Certified {code : Code P params before after} (p : Place catalog active code)
    (refs : Tuple (Port after) vars) : Prop :=
  Exit p refs ∧ ∀ holes : Rows P params before all,
    GoodRows catalog (fun r => p.embed (code.lift r)) holes →
    GoodRows catalog p.embed (code.rows holes p.embed (top active))

theorem straightBuildGood (b : Simple.Build P params before vars)
    (p : Place catalog active (.straight b.code))
    (valid : StraightBuildChecks (fun r => Visible catalog active (pos (p.embed (b.code.lift r)))) b) :
    Certified p b.refs := by
  constructor
  · intro t r
    have checked := straightGood b.code p _ (fun _ _ h => h) valid.1
    exact checked.1 t _ (valid.2 t r)
  · intro holes oldRows
    exact (straightGood b.code p _ (fun _ _ h => h) valid.1).2 holes oldRows

end Silmaril.SSA.PEG.Simple.Structured.Proofs

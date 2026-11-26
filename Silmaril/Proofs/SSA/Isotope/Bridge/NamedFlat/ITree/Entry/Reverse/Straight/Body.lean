module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.SSA.LambdaRTL
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA (Flat)
open LetCase.LocallyNameless (Tm)

universe u v
variable {Base V K : Type u} {F : Type v} {n m labels : Nat}
  [DecidableEq V] [DecidableEq Base] [HasTy F (Ty Base)]

/-- Current versions preserve the types of visible source registers. -/
def Scope (cur : V → Nat) (names : Names V n) (ctx : BoundCtx (Ty Base) n)
    (target : Names (V × Nat) m) (targetCtx : BoundCtx (Ty Base) m) : Prop :=
  ∀ reg i, names reg = some i →
    ∃ j, target (reg, cur reg) = some j ∧ targetCtx.get j = ctx.get i

omit [DecidableEq Base] [HasTy F (Ty Base)] in
private theorem push {cur : V → Nat} {names : Names V n} {ctx : BoundCtx (Ty Base) n}
    {target : Names (V × Nat) m} {targetCtx : BoundCtx (Ty Base) m}
    (scope : Scope cur names ctx target targetCtx)
    (reg : V) (A : Ty Base) (depth : Nat) :
    Scope (Version.setv cur reg (depth + 1)) (bindName names reg) (.snoc ctx A)
      (bindName target (reg, depth + 1)) (.snoc targetCtx A) := by
  intro r i found
  by_cases same : r = reg
  · subst r
    have eq : i = 0 := by simpa [bindName] using found.symm
    subst i
    exact ⟨0, by simp [Version.setv, bindName], rfl⟩
  · obtain ⟨slot, old, rfl⟩ := Option.map_eq_some_iff.mp (by
      simpa only [bindName, ite_eq_right same] using found)
    obtain ⟨j, hit, type⟩ := scope r slot old
    exact ⟨j.succ, by simp [Version.setv, bindName, same, hit], type⟩

omit [DecidableEq V] in
private theorem value_version {cur : V → Nat}
    {names : Names V n} {ctx : BoundCtx (Ty Base) n}
    {target : Names (V × Nat) m} {targetCtx : BoundCtx (Ty Base) m}
    (scope : Scope cur names ctx target targetCtx) (arg : Val V)
    {old : Tm Empty F n} (read : value names arg = some old) :
    ∃ next : Tm Empty F m, value target (Version.rn cur arg) = some next ∧
      infer targetCtx next = infer ctx old := by
  induction arg generalizing old with
  | var reg =>
    obtain ⟨i, found, rfl⟩ := Option.map_eq_some_iff.mp read
    obtain ⟨j, hit, type⟩ := scope reg i found
    exact ⟨.bv j, by simp [Version.rn, value, hit], congrArg some type⟩
  | unit =>
    cases read
    exact ⟨.unit, rfl, rfl⟩
  | pair left right ihLeft ihRight =>
    simp only [value, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨_, hl, _, hr, rfl⟩ := read
    obtain ⟨l, el, tl⟩ := ihLeft hl
    obtain ⟨r, er, tr⟩ := ihRight hr
    exact ⟨.pair l r, by simp [value, Version.rn, el, er], by simp [infer, tl, tr]⟩

omit [DecidableEq V] in
private theorem operand_version {cur : V → Nat}
    {names : Names V n} {ctx : BoundCtx (Ty Base) n}
    {target : Names (V × Nat) m} {targetCtx : BoundCtx (Ty Base) m}
    (scope : Scope cur names ctx target targetCtx) (op : Op V F)
    {old : Tm Empty F n} (read : operand names op = some old) :
    ∃ next : Tm Empty F m, operand target (Version.rnOp cur op) = some next ∧
      infer targetCtx next = infer ctx old := by
  cases op with
  | val arg => exact value_version scope arg read
  | app instr arg =>
    obtain ⟨_, found, rfl⟩ := Option.map_eq_some_iff.mp read
    obtain ⟨a, hit, type⟩ := value_version scope arg found
    exact ⟨.op instr a, by simp [operand, Version.rnOp, hit], by simp [infer, type]⟩
  | inl | inr | abort => cases read

variable [DecidableEq K]

private theorem version_let1 (dest : K → Option (List V)) (live : List V) (cur : V → Nat)
    (d : Nat) (x : V) (op : Op V F) (tail : CFG.Body V K F) :
    Versioning.versionBody (.let1 x op tail) dest live cur d =
      .let1 (x, d + 1) (Version.rnOp cur op)
        (Versioning.versionBody tail dest live (Version.setv cur x (d + 1)) (d + 1)) := by
  apply Option.get_of_eq_some
  simp only [CFG.Body.toRegion, Version.version, CFG.Body.ofRegion?]
  exact congrArg (Option.map (CFG.Body.let1 (x, d + 1) (Version.rnOp cur op))) (Option.some_get _).symm

private theorem version_let2 (dest : K → Option (List V)) (live : List V) (cur : V → Nat)
    (d : Nat) (x y : V) (op : Op V F) (tail : CFG.Body V K F) :
    Versioning.versionBody (.let2 x y op tail) dest live cur d =
      .let2 (x, d + 1) (y, d + 2) (Version.rnOp cur op)
        (Versioning.versionBody tail dest live
          (Version.setv (Version.setv cur x (d + 1)) y (d + 2)) (d + 2)) := by
  apply Option.get_of_eq_some
  simp only [CFG.Body.toRegion, Version.version, CFG.Body.ofRegion?]
  exact congrArg (Option.map (CFG.Body.let2 (x, d + 1) (y, d + 2) (Version.rnOp cur op)))
    (Option.some_get _).symm

/-- The branch interface classifies a numbered edge as an exit or as an
internal jump with an empty saved record. -/
def Routes (index : K → Option (Fin labels)) (dest : K → Option (List V))
    (old new : Fin labels → Ty Base) : Prop :=
  ∀ k i, index k = some i →
    (dest k = none ∧ new i = old i) ∨
      (dest k = some [] ∧ new i = .product (old i) .unit)

omit [DecidableEq V] [DecidableEq K] in
private theorem reify_term (r : Silmaril.SSA.LambdaRTL.Region V K F)
    {tail : CFG.Term V K F} (read : CFG.Term.ofRegion? r = some tail) :
    CFG.Body.ofRegion? r = some (.term tail) := by
  cases r with
  | br | case => exact congrArg (Option.map CFG.Body.term) read
  | let1 | let2 | join => cases read

/-- The reified terminator scopes each case arm using the version and type
of its own binder. Both arms start from the same incoming scope. -/
private theorem version_term (index : K → Option (Fin labels)) (dest : K → Option (List V))
    (oldTypes newTypes : Fin labels → Ty Base) (routes : Routes index dest oldTypes newTypes)
    (live : List V) (src : CFG.Term V K F) (d : Nat) (cur : V → Nat)
    (names : Names V n) (ctx : BoundCtx (Ty Base) n)
    (target : Names (V × Nat) m) (targetCtx : BoundCtx (Ty Base) m)
    (scope : Scope cur names ctx target targetCtx)
    {old : Flat F labels n} (read : term index names src = some old)
    (checked : checkBody oldTypes ctx old = true) :
    ∃ named next, CFG.Term.ofRegion? (Version.version dest live cur d src.toRegion) = some named ∧
      term index target named = some next ∧ checkBody newTypes targetCtx next = true := by
  induction src generalizing n m d cur with
  | br label arg =>
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨i, hit, exp, hExp, rfl⟩ := read
    obtain ⟨e, he, ty⟩ := value_version scope arg hExp
    have hType : infer targetCtx e = some (oldTypes i) := ty.trans (of_decide_eq_true checked)
    rcases routes label i hit with ⟨route, same⟩ | ⟨route, packed⟩
    · exact ⟨.br label (Version.rn cur arg), .br i e,
        by simp [CFG.Term.toRegion, Version.version, route, CFG.Term.ofRegion?],
        by simp [term, hit, he], by simp [checkBody, hType, same]⟩
    · exact ⟨.br label (.pair (Version.rn cur arg) .unit), .br i (.pair e .unit),
        by simp [CFG.Term.toRegion, Version.version, route, CFG.Term.ofRegion?, Version.pack],
        by simp [term, hit, value, he], by simp [checkBody, infer, hType, packed]⟩
  | case op x left y right ihLeft ihRight =>
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨opOld, hOp, lOld, hLeft, rOld, hRight, rfl⟩ := read
    obtain ⟨e, he, ty⟩ := operand_version scope op hOp
    cases inferred : infer ctx opOld with
    | none => simp [checkBody, inferred] at checked
    | some type =>
      cases type <;> simp only [checkBody, inferred, Bool.false_eq_true, Bool.and_eq_true] at checked
      case coprod A B =>
        obtain ⟨l, lFlat, lReified, lRead, lTyped⟩ :=
          ihLeft (d + 1) _ _ _ _ _ (push scope x A d) hLeft checked.1
        obtain ⟨r, rFlat, rReified, rRead, rTyped⟩ :=
          ihRight (d + 1) _ _ _ _ _ (push scope y B d) hRight checked.2
        exact ⟨.case (Version.rnOp cur op) (x, d + 1) l (y, d + 1) r, .case e lFlat rFlat,
          by simp [CFG.Term.toRegion, Version.version, CFG.Term.ofRegion?, lReified, rReified],
          by simp [term, he, lRead, rRead], by simp [checkBody, ty, inferred, lTyped, rTyped]⟩

/-- Every supported source constructor reads back and passes local typing
after the actual versioner has renamed the registers and wrapped the jumps. -/
theorem version_body (index : K → Option (Fin labels)) (dest : K → Option (List V))
    (oldTypes newTypes : Fin labels → Ty Base) (routes : Routes index dest oldTypes newTypes)
    (live : List V) (src : CFG.Body V K F)
    (d : Nat) (cur : V → Nat)
    (names : Names V n) (ctx : BoundCtx (Ty Base) n)
    (target : Names (V × Nat) m) (targetCtx : BoundCtx (Ty Base) m)
    (scope : Scope cur names ctx target targetCtx)
    {old : Flat F labels n} (read : body index names src = some old)
    (checked : checkBody oldTypes ctx old = true) :
    ∃ next, body index target (Versioning.versionBody src dest live cur d) = some next ∧
      checkBody newTypes targetCtx next = true := by
  induction src generalizing n m d cur with
  | term tail =>
    obtain ⟨named, next, parsed, readNext, typed⟩ :=
      version_term index dest oldTypes newTypes routes live tail d cur names ctx target targetCtx scope read checked
    have actual : Versioning.versionBody (.term tail) dest live cur d = .term named :=
      Option.get_of_eq_some _ (reify_term _ parsed)
    rw [actual]
    exact ⟨next, readNext, typed⟩
  | let1 x op tail ih =>
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨exp, expRead, rest, restRead, rfl⟩ := read
    obtain ⟨e, he, ty⟩ := operand_version scope op expRead
    cases h : infer ctx exp with
    | none => simp [checkBody, h] at checked
    | some A =>
      have hTail : checkBody oldTypes (.snoc ctx A) rest = true := by simpa [checkBody, h] using checked
      obtain ⟨b, hb, ht⟩ := ih (d + 1) _ _ _ _ _ (push scope x A d) restRead hTail
      exact ⟨.let₁ e b, by simp [version_let1, body, he, hb], by simp [checkBody, ty, h, ht]⟩
  | let2 x y op tail ih =>
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨exp, expRead, rest, restRead, rfl⟩ := read
    obtain ⟨e, he, ty⟩ := operand_version scope op expRead
    cases h : infer ctx exp with
    | none => simp [checkBody, h] at checked
    | some T =>
      cases T <;> simp only [checkBody, h, Bool.false_eq_true] at checked
      case product A B =>
        obtain ⟨b, hb, ht⟩ := ih (d + 2) _ _ _ _ _
          (push (push scope x A d) y B (d + 1)) restRead checked
        exact ⟨.let₂ e b, by simp [version_let2, body, he, hb], by simp [checkBody, ty, h, ht]⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight

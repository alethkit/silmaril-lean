module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Defs
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Proofs

universe u v w
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}}
variable {ρ : Type (max u w)} {value : V → Type (max u w)}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

set_option backward.isDefEq.respectTransparency false

private theorem get_runtime {F : Ty V → Type w} (rt : F runtime) (xs : Tuple F outs) :
    (withRuntime rt xs).get (runtimePort outs) = rt := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem split_append {F : Ty V → Type w} (rt : F runtime) (xs : Tuple F outs) :
    splitRuntime outs (withRuntime rt xs) = (xs, rt) := by
  induction xs with
  | nil => rfl
  | cons x _ ih => simp only [withRuntime, splitRuntime, ih]

private theorem append_split {F : Ty V → Type w} (xs : Tuple F (Threaded outs)) :
    withRuntime (splitRuntime outs xs).2 (splitRuntime outs xs).1 = xs := by
  induction outs with
  | nil => cases xs with | cons _ tail => cases tail; rfl
  | cons _ _ ih =>
    cases xs with
    | cons x xs => exact congrArg (Tuple.cons x) (ih xs)

private theorem get_newest {F : Ty V → Type w} {head : Ports (Ty V)} {t : Ty V}
    (locals : Locals F past) (xs : Tuple F head) (p : Port head t) :
    ((locals.snoc xs).get (newestIndex head past)).get (newestPort p past) = xs.get p := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact ih locals.2

private theorem read_cons {F : Ty V → Type w} {t : Ty V}
    (o : Origin args past t) (wires : Wires args past outs)
    (entry : Tuple F args) (locals : Locals F past) :
    Wires.read (.cons o wires) entry locals =
      .cons (readOrigin o entry locals) (wires.read entry locals) := by
  cases o <;> rfl

private theorem read_appended {F : Ty V → Type w} (live : Origin args past runtime)
    (wires : Wires args past outs) (entry : Tuple F args) (locals : Locals F past) :
    Wires.read (withRuntime live wires) entry locals =
      withRuntime (readOrigin live entry locals) (wires.read entry locals) := by
  induction wires with
  | nil => cases live <;> rfl
  | cons _ _ ih => exact congrArg (Tuple.cons _) ih

private theorem erase_get (xs : Tuple (RuntimeValues value ρ) outs) {t : Ty V} (p : Port outs t) :
    (eraseTuple xs).get p = eraseValue t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs; exact ih _

private theorem erase_lookup (past : List (Ports (Ty V)))
    (locals : Locals (RuntimeValues value ρ) past) (i : Fin past.length) :
    (eraseLocals past locals).get i = eraseTuple (locals.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons _ _ ih => exact Fin.cases rfl (fun j => ih locals.2 j) i

private theorem erase_origin {t : Ty V} (o : Origin args past t)
    (entry : Tuple (RuntimeValues value ρ) args) (locals : Locals (RuntimeValues value ρ) past) :
    readOrigin o (eraseTuple entry) (eraseLocals past locals) =
      eraseValue t (readOrigin o entry locals) := by
  cases o with
  | arg p => exact erase_get entry p
  | output i p => simp only [readOrigin, erase_lookup, erase_get]

private theorem erase_read (wires : Wires args past outs)
    (entry : Tuple (RuntimeValues value ρ) args) (locals : Locals (RuntimeValues value ρ) past) :
    wires.read (eraseTuple entry) (eraseLocals past locals) = eraseTuple (wires.read entry locals) := by
  induction wires with
  | nil => rfl
  | @cons t _ o rest ih =>
    rw [read_cons, read_cons]
    change Tuple.cons (readOrigin o (eraseTuple entry) (eraseLocals past locals))
      (Wires.read rest (eraseTuple entry) (eraseLocals past locals)) =
      Tuple.cons (eraseValue t (readOrigin o entry locals)) (eraseTuple (Wires.read rest entry locals))
    rw [erase_origin, ih]

private theorem erase_snoc (locals : Locals (RuntimeValues value ρ) past)
    (xs : Tuple (RuntimeValues value ρ) outs) :
    eraseLocals (past ++ [outs]) (locals.snoc xs) = (eraseLocals past locals).snoc (eraseTuple xs) := by
  induction past with
  | nil => rfl
  | cons _ _ ih =>
    change (eraseTuple locals.1, eraseLocals _ (locals.2.snoc xs)) =
      (eraseTuple locals.1, (eraseLocals _ locals.2).snoc (eraseTuple xs))
    rw [ih]

private theorem erase_append (rt : ρ) (xs : Tuple (RuntimeValues value ρ) outs) :
    eraseTuple (withRuntime rt xs) = withRuntime PUnit.unit (eraseTuple xs) := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Tuple.cons _) ih

private theorem erase_restore (rt : ρ) (xs : Tuple (Values value) outs) :
    eraseTuple (xs.map (restoreValue rt)) = xs := by
  induction xs with
  | nil => rfl
  | @cons t _ x xs ih =>
    have head : eraseValue (value := value) t (restoreValue rt t x) = x := by
      cases t <;> rfl
    change Tuple.cons (eraseValue t (restoreValue rt t x))
      (eraseTuple (xs.map (restoreValue rt))) = .cons x xs
    rw [head, ih]

private theorem restore_erase (data : Data outs) (rt : ρ)
    (xs : Tuple (RuntimeValues value ρ) outs) :
    (eraseTuple xs).map (restoreValue rt) = xs := by
  induction data with
  | nil => cases xs; rfl
  | value _ ih => cases xs with | cons x xs => exact congrArg (Tuple.cons x) (ih xs)
  | control _ ih => cases xs with | cons x xs => exact congrArg (Tuple.cons x) (ih xs)

private theorem erase_decode (result : Tuple (Values value) outs × ρ) :
    eraseTuple (decode result) = withRuntime PUnit.unit result.1 := by
  simp only [decode, erase_append, erase_restore]

private theorem next_decode (locals : Locals (RuntimeValues value ρ) past)
    (result : Tuple (Values value) outs × ρ) (entry : Tuple (RuntimeValues value ρ) args) :
    readOrigin (nextRuntime past outs) entry (locals.snoc (decode result)) = result.2 := by
  simp only [nextRuntime, readOrigin, get_newest, decode, get_runtime]

theorem denote_transport {M : Type (max u w) → Type (max u w)} [Monad M] (m : Model P E M)
    {a : Data args} {b : Data outs}
    {s t : Term (Opcode P E) (Threaded args) [] sigs (Threaded outs)}
    (eq : s = t) (checked : EntryChecked a b t) :
    Checked.denote m (eq.symm ▸ checked : EntryChecked a b s) = checked.denote m := by
  cases eq
  rfl

variable (m : Model P E (StateM ρ))

/-- At each numbered prefix the sole live runtime is the initial state of
the corresponding computation. The numbered locals keep only their pure
component in the monadic fold. -/
theorem eval_agrees {a : Data args} {b : Data outs}
    {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked P E a b live t)
    (entry : Tuple (RuntimeValues m.value ρ) (Threaded args))
    (locals : Locals (RuntimeValues m.value ρ) past) :
    decode ((checked.eval m (eraseTuple entry) (eraseLocals past locals)).run
      (readOrigin live entry locals)) = t.eval m.toRVSDG entry locals := by
  induction checked with
  | @ret args outs a b past live wires =>
    simp only [Checked.eval, Term.eval, read_appended, erase_read]
    change withRuntime _ ((eraseTuple (wires.read entry locals)).map (restoreValue _)) = _
    rw [restore_erase b]
    rfl
  | @bind args outs ins out a b past sigs live i o op wires rest checked ih =>
    simp only [Checked.eval, Term.eval, primitiveNode, Shape.eval, Model.toRVSDG,
      read_appended, split_append, erase_read]
    let result := (m.step op (eraseTuple (wires.read entry locals))).run
      (readOrigin live entry locals)
    have continued := ih entry (locals.snoc (decode result))
    rw [erase_snoc, erase_decode, next_decode] at continued
    exact continued
  | @gamma args outs ins out a b past sigs extra choice live i o wires childSigs
      children rest arms checked ihArms ih =>
    let tag := (readOrigin choice entry locals).down
    let data := wires.read entry locals
    let rt := readOrigin live entry locals
    let result := ((arms tag).eval m (withRuntime PUnit.unit (eraseTuple data)) PUnit.unit).run rt
    have arm := ihArms tag (withRuntime rt data) PUnit.unit
    change decode (((arms tag).eval m (eraseTuple (withRuntime rt data)) PUnit.unit).run
      ((withRuntime rt data).get (runtimePort ins))) = (children tag).eval (past := []) m.toRVSDG _ _ at arm
    rw [get_runtime, erase_append] at arm
    have continued := ih entry (locals.snoc (decode result))
    rw [erase_snoc, erase_decode, next_decode] at continued
    simp only [Checked.eval, Term.eval, gammaNode, Shape.eval, read_cons, read_appended]
    change decode (((arms (readOrigin choice (eraseTuple entry) (eraseLocals past locals)).down).eval m
      (withRuntime PUnit.unit (wires.read (eraseTuple entry) (eraseLocals past locals))) PUnit.unit >>=
      fun output => checked.eval m (eraseTuple entry)
        ((eraseLocals past locals).snoc (withRuntime PUnit.unit output))).run rt) = _
    rw [erase_origin, erase_read]
    change decode ((checked.eval m (eraseTuple entry)
      ((eraseLocals past locals).snoc (withRuntime PUnit.unit result.1))).run result.2) =
      rest.eval m.toRVSDG entry (locals.snoc ((children tag).eval (past := []) m.toRVSDG
        (withRuntime rt data) PUnit.unit))
    rw [← arm]
    exact continued

theorem denote_agrees {a : Data args} {b : Data outs}
    (g : Graph (Opcode P E) (Threaded args) [] sigs (Threaded outs))
    (checked : EntryChecked a b g.toTerm)
    (input : Tuple (RuntimeValues m.value ρ) (Threaded args)) :
    decode ((denoteGraph m g checked (eraseTuple (splitRuntime args input).1)).run
      (splitRuntime args input).2) = g.run m.toRVSDG input := by
  rw [← Graph.run_toTerm]
  have step := eval_agrees m checked (withRuntime (splitRuntime args input).2 (splitRuntime args input).1)
    PUnit.unit
  rw [erase_append] at step
  change decode (((checked.eval m _ PUnit.unit)).run
    ((withRuntime (splitRuntime args input).2 (splitRuntime args input).1).get (runtimePort args))) = _
    at step
  rw [get_runtime, append_split] at step
  exact step

end Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Proofs

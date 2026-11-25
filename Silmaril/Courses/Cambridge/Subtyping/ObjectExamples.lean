module

public import Silmaril.Courses.Cambridge.Subtyping.L3Examples
public import Silmaril.Courses.Cambridge.L3.NamedSyntax
import Silmaril.Courses.Cambridge.L3.Metatheory.SubstitutionAlgebra

/-! # Chapter 6 object generators and method reuse

Sewell, *Semantics of Programming Languages*, 12 February 2026,
p. 86 (slide 219) and p. 87 (slides 220–221). The source terms use the
existing L3 records, references, functions and strict let. The notes'
`()` is L3's `skip`. The declarations on p. 87 are typed under their
printed dependency on `counterClass`, then closed with its let binding
when examining their reductions.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Subtyping.Examples.Objects

open L3 (Ty Expr RawExpr IsValue Value Store Step Steps Config LocTypes VarTypes Loc)

def counterRepType : Ty := .record labelsP (fun _ => .ref .int)

def rawCounterFields (cell : RawExpr) (i : counterLabels.Index) : RawExpr :=
  if i.val = 0 then .lam "y" .unit (.deref cell)
  else .lam "y" .unit (.assign cell (.binary (.int 1) .add (.deref cell)))

def rawObjectGenerator : RawExpr :=
  .lam "y" .unit
    (.letE "x" (.ref .int) (.ref (.int 0))
      (.record counterLabels (rawCounterFields (.var "x"))))

/-- Slide 219's complete expression calls the freshly generated counter's increment. -/
def objectGenerator : Expr :=
  (RawExpr.letE "newCounter" (.arr .unit counterType) rawObjectGenerator
    (.app (.project (.app (.var "newCounter") .skip) "inc") .skip)).resolve []

private theorem counterFields_typed {Θ : LocTypes} {Γ : VarTypes} {ρ : List L3.Var}
    {cell : RawExpr} (reference : HasType Θ (Γ.push .unit) (cell.resolve ("y" :: ρ)) (.ref .int)) :
    HasType Θ Γ ((RawExpr.record counterLabels (rawCounterFields cell)).resolve ρ) counterType := by
  apply Typing.record
  intro i
  by_cases get : i.val = 0 <;> simp only [rawCounterFields, get, ite_true, ite_false,
    RawExpr.resolve, counterMethodType]
  · exact .lam (.deref reference)
  · exact .lam (.assign reference (.add (.int 1) (.deref reference)))

theorem objectGenerator_typed : HasType ∅ .empty objectGenerator .unit := by
  apply Typing.letE
  · exact .lam (.letE (.ref (.int 0)) (counterFields_typed (.bvar rfl)))
  · exact .app (.project (labels := counterLabels) (types := counterMethodType)
      1 (.app (.bvar rfl) .skip)) .skip

def counterClassType : Ty := .arr counterRepType counterType

def rawCounterClass : RawExpr :=
  .lam "x" counterRepType (.record counterLabels (rawCounterFields (.project (.var "x") "p")))

/-- The class takes a representation and closes each method over it. -/
def counterClass : Expr := rawCounterClass.resolve []

def rawRepresentation (cell : RawExpr) : RawExpr := .record labelsP (fun _ => cell)

def rawClassGenerator : RawExpr :=
  .lam "y" .unit
    (.letE "x" counterRepType (rawRepresentation (.ref (.int 0)))
      (.app (.var "counterClass") (.var "x")))

/-- Slide 220's second declaration, with the first declaration in scope. -/
def classGenerator : Expr := rawClassGenerator.resolve ["counterClass"]

def rawResetFields (i : resetCounterLabels.Index) : RawExpr :=
  if i.val = 0 then .project (.var "super") "get"
  else if i.val = 1 then .project (.var "super") "inc"
  else .lam "y" .unit (.assign (.project (.var "x") "p") (.int 0))

def rawResetCounterClass : RawExpr :=
  .lam "x" counterRepType
    (.letE "super" counterType (.app (.var "counterClass") (.var "x"))
      (.record resetCounterLabels rawResetFields))

/-- Slide 221's method-reuse declaration, with `counterClass` in scope. -/
def resetCounterClass : Expr := rawResetCounterClass.resolve ["counterClass"]

theorem counterClass_typed (Θ : LocTypes) : HasType Θ .empty counterClass counterClassType :=
  .lam (counterFields_typed (.project (labels := labelsP) (types := fun _ => .ref .int) 0 (.bvar rfl)))

theorem classGenerator_typed (Θ : LocTypes) :
    HasType Θ (VarTypes.empty.push counterClassType) classGenerator (.arr .unit counterType) :=
  .lam (.letE (.record (fun _ => .ref (.int 0))) (.app (.bvar rfl) (.bvar rfl)))

theorem resetCounterClass_typed (Θ : LocTypes) :
    HasType Θ (VarTypes.empty.push counterClassType) resetCounterClass (.arr counterRepType resetCounterType) := by
  apply Typing.lam
  refine .letE (.app (.bvar rfl) (.bvar rfl)) (.record ?_)
  intro i
  by_cases get : i.val = 0
  · simp only [rawResetFields, get, ite_true, RawExpr.resolve, counterMethodType]
    exact .project (labels := counterLabels) (types := counterMethodType) 0 (.bvar rfl)
  · by_cases inc : i.val = 1
    · simp only [rawResetFields, inc, ite_true, counterMethodType]
      exact .project (labels := counterLabels) (types := counterMethodType) 1 (.bvar rfl)
    · simp only [rawResetFields, get, inc, ite_false, RawExpr.resolve, counterMethodType]
      exact .lam (.assign (.project (labels := labelsP) (types := fun _ => .ref .int) 0 (.bvar rfl)) (.int 0))

theorem counterFields_ready (cell : RawExpr) (i : counterLabels.Index) :
    IsValue ((rawCounterFields cell i).resolve []) := by
  by_cases get : i.val = 0 <;>
    simp only [rawCounterFields, get, ite_true, ite_false, RawExpr.resolve] <;> exact .lam _ _

/-- A method record whose fields are lambda values, even when their bodies
refer to a store cell. -/
def counterObject (cell : RawExpr) : Value :=
  ⟨(RawExpr.record counterLabels (rawCounterFields cell)).resolve [], .record (counterFields_ready cell)⟩

def cellStore (address : Loc) (n : Int) : Store :=
  (∅ : Store).insert address ⟨.int n, .int n⟩

private theorem cell_read (address : Loc) (n : Int) :
    (cellStore address n).lookup address = some ⟨.int n, .int n⟩ := by simp [cellStore]

private theorem cell_write (address : Loc) (before after : Int) :
    Step ⟨.assign (.loc address) (.int after), cellStore address before⟩
      ⟨.skip, cellStore address after⟩ := by
  simpa only [cellStore, Finmap.insert_insert] using
    Step.assignValue ⟨.int after, .int after⟩ (s := cellStore address before)
      (loc := address) (Finmap.mem_of_lookup_eq_some (cell_read address before))

private theorem increment_cell (address : Loc) (n : Int) :
    Steps ⟨.assign (.loc address) (.binary (.int 1) .add (.deref (.loc address))), cellStore address n⟩
      ⟨.skip, cellStore address (1 + n)⟩ :=
  .head (.assignRight (.binaryRight (.int 1) (.derefValue (cell_read address n))))
    (.head (.assignRight (.add 1 n _)) (.single (cell_write address n (1 + n))))

/-- Slide 219 increments the newly allocated zero cell and returns unit. -/
theorem objectGenerator_trace (address : Loc) :
    Steps ⟨objectGenerator, ∅⟩ ⟨.skip, cellStore address 1⟩ := by
  let methods := (RawExpr.record counterLabels (rawCounterFields (.var "x"))).resolve ["x", "y"]
  have unchanged : methods.subst (Expr.liftSubst (fun
      | 0 => .skip
      | i + 1 => .bvar i)) = methods := by
    apply congrArg (Expr.record counterLabels)
    funext i
    by_cases get : i.val = 0 <;>
      simp only [rawCounterFields, get, ite_true, ite_false, RawExpr.resolve, Expr.subst] <;> rfl
  have callGenerator : Step ⟨.app (rawObjectGenerator.resolve []) .skip, ∅⟩
      ⟨.letE (.ref .int) (.ref (.int 0)) methods, ∅⟩ := by
    conv_rhs => rw [← unchanged]
    exact .appFun .skip
  have allocation : Step ⟨.ref (.int 0), ∅⟩ ⟨.loc address, cellStore address 0⟩ :=
    .refValue ⟨.int 0, .int 0⟩ Finmap.notMem_empty
  refine .head (.letValue (.lam _ _)) (.head (.appLeft (.projectStep callGenerator)) ?_)
  refine .head (.appLeft (.projectStep (.letStep allocation))) ?_
  let stored := counterObject (.loc address)
  have payload : ((RawExpr.record counterLabels (rawCounterFields (.var "x"))).resolve
      ["x", "y"]).beta (.loc address) = stored.val := by
    apply congrArg (Expr.record counterLabels)
    funext i
    by_cases get : i.val = 0 <;>
      simp only [rawCounterFields, get, ite_true, ite_false, RawExpr.resolve, Expr.subst] <;> rfl
  have bindLocation : Step ⟨.letE (.ref .int) (.loc address)
      ((RawExpr.record counterLabels (rawCounterFields (.var "x"))).resolve ["x", "y"]),
      cellStore address 0⟩ ⟨stored.val, cellStore address 0⟩ := by
    rw [← payload]
    exact .letValue (.loc address)
  refine .head (.appLeft (.projectStep bindLocation)) ?_
  exact .head (.appLeft (.projectValue (labels := counterLabels) 1 (counterFields_ready (.loc address))))
    (.head (.appFun .skip) (increment_cell address 0))

private theorem counterClass_subst (σ : Nat → Expr) : counterClass.subst σ = counterClass := by
  apply congrArg (Expr.lam counterRepType)
  apply congrArg (Expr.record counterLabels)
  funext i
  by_cases get : i.val = 0 <;>
    simp only [rawCounterFields, get, ite_true, ite_false, RawExpr.resolve, Expr.subst] <;> rfl

private theorem counterClass_rename (ρ : Nat → Nat) : counterClass.rename ρ = counterClass := by
  rw [← (counterClass.rename ρ).subst_id, Expr.subst_rename, counterClass_subst]

def representation (address : Loc) : Value :=
  ⟨(rawRepresentation (.loc address)).resolve [], .record (fun _ => .loc _)⟩

def representedCell (address : Loc) : RawExpr :=
  .project (rawRepresentation (.loc address)) "p"

/-- Applying the class reuses the supplied reference without allocating. -/
theorem counterClass_step (address : Loc) (s : Store) :
    Step ⟨.app counterClass (representation address).val, s⟩
      ⟨(counterObject (representedCell address)).val, s⟩ := by
  let body := (RawExpr.record counterLabels (rawCounterFields (.project (.var "x") "p"))).resolve ["x"]
  have binds : body.beta (representation address).val =
      (counterObject (representedCell address)).val := by
    apply congrArg (Expr.record counterLabels)
    funext i
    by_cases get : i.val = 0 <;>
      simp only [rawCounterFields, get, ite_true, ite_false, RawExpr.resolve, Expr.subst] <;> rfl
  rw [← binds]
  exact .appFun (representation address).property

/-- Close slide 220's two declarations, then call its `newCounter` with unit. -/
def classConstruction : Expr :=
  (RawExpr.letE "counterClass" counterClassType rawCounterClass
    (.letE "newCounter" (.arr .unit counterType) rawClassGenerator
      (.app (.var "newCounter") .skip))).resolve []

theorem classConstruction_typed : HasType ∅ .empty classConstruction counterType :=
  .letE (counterClass_typed _) (.letE (classGenerator_typed _) (.app (.bvar rfl) .skip))

private theorem representation_allocation (address : Loc) :
    Step ⟨(rawRepresentation (.ref (.int 0))).resolve [], ∅⟩
      ⟨(representation address).val, cellStore address 0⟩ := by
  have allocate : Step ⟨.ref (.int 0), ∅⟩ ⟨.loc address, cellStore address 0⟩ :=
    .refValue ⟨.int 0, .int 0⟩ Finmap.notMem_empty
  have before (j : labelsP.Index) (earlier : j < 0) : IsValue (.ref (.int 0)) :=
    (Nat.not_lt_zero j.val earlier).elim
  have fields : Function.update (fun _ : labelsP.Index => Expr.ref (.int 0)) 0 (.loc address) =
      fun _ => .loc address := by
    funext i
    have only : i = 0 := Fin.ext (Nat.le_zero.mp (Nat.le_of_lt_succ i.isLt))
    subst i
    exact Function.update_self _ _ _
  change Step ⟨.record labelsP (fun _ => .ref (.int 0)), ∅⟩
    ⟨.record labelsP (fun _ => .loc address), cellStore address 0⟩
  rw [← fields]
  exact .recordStep (labels := labelsP) 0 before allocate

theorem classConstruction_trace (address : Loc) :
    Steps ⟨classConstruction, ∅⟩
      ⟨(counterObject (representedCell address)).val, cellStore address 0⟩ := by
  let body := Expr.app counterClass (.bvar 0)
  let generator := Expr.lam .unit
    (.letE counterRepType ((rawRepresentation (.ref (.int 0))).resolve []) body)
  have close : classGenerator.beta counterClass = generator := by
    change Expr.lam .unit (.letE counterRepType (.record labelsP (fun _ => .ref (.int 0)))
      (.app ((counterClass.rename Nat.succ).rename Nat.succ) (.bvar 0))) = generator
    rw [counterClass_rename, counterClass_rename]
    rfl
  have enter : Step ⟨classConstruction, ∅⟩
      ⟨.letE (.arr .unit counterType) generator (.app (.bvar 0) .skip), ∅⟩ := by
    rw [← close]
    exact .letValue (.lam _ _)
  have call : Step ⟨.app generator .skip, ∅⟩
      ⟨.letE counterRepType ((rawRepresentation (.ref (.int 0))).resolve []) body, ∅⟩ := by
    have beta := Step.appFun (s := ∅) (domain := .unit) (body := .letE counterRepType
      ((rawRepresentation (.ref (.int 0))).resolve []) body) IsValue.skip
    change Step ⟨.app generator .skip, ∅⟩
      ⟨.letE counterRepType ((rawRepresentation (.ref (.int 0))).resolve [])
        (.app (counterClass.subst _) (.bvar 0)), ∅⟩ at beta
    rw [counterClass_subst] at beta
    exact beta
  have bindRep : Step ⟨.letE counterRepType (representation address).val body, cellStore address 0⟩
      ⟨.app counterClass (representation address).val, cellStore address 0⟩ := by
    have beta := Step.letValue (s := cellStore address 0) (T := counterRepType) (body := body)
      (representation address).property
    change Step ⟨.letE counterRepType (representation address).val body, cellStore address 0⟩
      ⟨.app (counterClass.subst _) (representation address).val, cellStore address 0⟩ at beta
    rw [counterClass_subst] at beta
    exact beta
  exact .head enter (.head (.letValue (.lam _ _)) (.head call
    (.head (.letStep (representation_allocation address))
      (.head bindRep (.single (counterClass_step address _))))))

/-- Close slide 221's declaration and supply a representation for an
already allocated cell. -/
def resetConstruction (address : Loc) : Expr :=
  (RawExpr.letE "counterClass" counterClassType rawCounterClass
    (.app rawResetCounterClass (rawRepresentation (.loc address)))).resolve []

theorem resetConstruction_typed {Θ : LocTypes} {address : Loc}
    (allocated : Θ.lookup address = some .int) :
    HasType Θ .empty (resetConstruction address) resetCounterType :=
  .letE (counterClass_typed Θ) (.app (resetCounterClass_typed Θ) (.record (fun _ => .loc allocated)))

def resetMethod (address : Loc) : Expr :=
  (.lam .unit (.assign ((representedCell address).resolve []) (.int 0)))

def reusedFields (address : Loc) (i : resetCounterLabels.Index) : Expr :=
  if i.val = 0 then (rawCounterFields (representedCell address) 0).resolve []
  else if i.val = 1 then (rawCounterFields (representedCell address) 1).resolve []
  else resetMethod address

theorem reusedFields_ready (address : Loc) (i : resetCounterLabels.Index) :
    IsValue (reusedFields address i) := by
  unfold reusedFields
  split
  · exact counterFields_ready (representedCell address) 0
  split
  · exact counterFields_ready (representedCell address) 1
  · exact .lam _ _

def resetObject (address : Loc) : Value :=
  ⟨.record resetCounterLabels (reusedFields address), .record (reusedFields_ready address)⟩

private def parentFields (address : Loc) (i : resetCounterLabels.Index) : Expr :=
  if i.val = 0 then .project (counterObject (representedCell address)).val "get"
  else if i.val = 1 then .project (counterObject (representedCell address)).val "inc"
  else resetMethod address

private theorem reuse_projections (address : Loc) (s : Store) :
    Steps ⟨.record resetCounterLabels (parentFields address), s⟩ ⟨(resetObject address).val, s⟩ := by
  let cell := representedCell address
  let first := Function.update (parentFields address) 0 ((rawCounterFields cell 0).resolve [])
  let second := Function.update first 1 ((rawCounterFields cell 1).resolve [])
  have firstStep : Step ⟨.record resetCounterLabels (parentFields address), s⟩
      ⟨.record resetCounterLabels first, s⟩ := by
    apply Step.recordStep (labels := resetCounterLabels) 0
    · intro i earlier
      exact (Nat.not_lt_zero i.val earlier).elim
    · exact .projectValue (labels := counterLabels) 0 (counterFields_ready cell)
  have secondStep : Step ⟨.record resetCounterLabels first, s⟩
      ⟨.record resetCounterLabels second, s⟩ := by
    apply Step.recordStep (labels := resetCounterLabels) 1
    · intro i earlier
      have zero : i = 0 := Fin.ext (Nat.lt_one_iff.mp earlier)
      subst i
      simpa only [first, Function.update_self] using counterFields_ready cell 0
    · change Step ⟨Function.update (parentFields address) 0 _ 1, s⟩ _
      rw [Function.update_of_ne (show (1 : resetCounterLabels.Index) ≠ 0 by decide)]
      exact .projectValue (labels := counterLabels) 1 (counterFields_ready cell)
  have equal : second = reusedFields address := by
    funext i
    by_cases get : i.val = 0
    · have zero : i = 0 := Fin.ext get
      subst i
      simp only [second, first, Function.update_of_ne (show (0 : resetCounterLabels.Index) ≠ 1 by decide),
        Function.update_self]
      rfl
    · by_cases inc : i.val = 1
      · have one : i = 1 := Fin.ext inc
        subst i
        simp only [second, Function.update_self]
        rfl
      · have notGet : i ≠ 0 := fun equal => get (congrArg Fin.val equal)
        have notInc : i ≠ 1 := fun equal => inc (congrArg Fin.val equal)
        simp only [second, first, Function.update_of_ne notGet, Function.update_of_ne notInc,
          parentFields, reusedFields, get, inc, ite_false]
  change Steps _ ⟨.record resetCounterLabels (reusedFields address), s⟩
  rw [← equal]
  exact .head firstStep (.single secondStep)

/-- The inherited fields are the original class's closures on the very
same representation. Constructing the resettable object leaves the store
as it was. -/
theorem resetConstruction_trace (address : Loc) (s : Store) :
    Steps ⟨resetConstruction address, s⟩ ⟨(resetObject address).val, s⟩ := by
  let fields := fun i => (rawResetFields i).resolve ["super", "x", "counterClass"]
  let resetFn := Expr.lam counterRepType
    (.letE counterType (.app counterClass (.bvar 0)) (.record resetCounterLabels fields))
  let σ : Nat → Expr := fun
    | 0 => counterClass
    | i + 1 => .bvar i
  have close : resetCounterClass.beta counterClass = resetFn := by
    change Expr.lam counterRepType (.letE counterType (.app (counterClass.rename Nat.succ) (.bvar 0))
      (.record resetCounterLabels (fun i => (fields i).subst (Expr.liftSubst (Expr.liftSubst σ))))) = resetFn
    rw [counterClass_rename]
    apply congrArg (fun bodies => Expr.lam counterRepType
      (.letE counterType (.app counterClass (.bvar 0)) (.record resetCounterLabels bodies)))
    funext i
    by_cases get : i.val = 0
    · simp only [fields, rawResetFields, get, ite_true, RawExpr.resolve, Expr.subst]
      rfl
    · by_cases inc : i.val = 1
      · simp only [fields, rawResetFields, inc, ite_true]
        rfl
      · simp only [fields, rawResetFields, get, inc, ite_false, RawExpr.resolve, Expr.subst]
        rfl
  let rep := representation address
  let τ : Nat → Expr := fun
    | 0 => rep.val
    | i + 1 => .bvar i
  let methods := fun i => (fields i).subst (Expr.liftSubst τ)
  have enter : Step ⟨resetConstruction address, s⟩ ⟨.app resetFn rep.val, s⟩ := by
    rw [← close]
    exact .letValue (.lam _ _)
  have call : Step ⟨.app resetFn rep.val, s⟩
      ⟨.letE counterType (.app counterClass rep.val) (.record resetCounterLabels methods), s⟩ := by
    have beta := Step.appFun (s := s) (domain := counterRepType)
      (body := .letE counterType (.app counterClass (.bvar 0)) (.record resetCounterLabels fields))
      rep.property
    change Step ⟨.app resetFn rep.val, s⟩
      ⟨.letE counterType (.app (counterClass.subst τ) rep.val) (.record resetCounterLabels methods), s⟩ at beta
    rw [counterClass_subst] at beta
    exact beta
  let parent := counterObject (representedCell address)
  have unpack : (Expr.record resetCounterLabels methods).beta parent.val =
      .record resetCounterLabels (parentFields address) := by
    apply congrArg (Expr.record resetCounterLabels)
    funext i
    by_cases get : i.val = 0
    · simp only [methods, fields, rawResetFields, parentFields, get, ite_true, RawExpr.resolve, Expr.subst]
      rfl
    · by_cases inc : i.val = 1
      · simp only [methods, fields, rawResetFields, parentFields, inc, ite_true]
        rfl
      · simp only [methods, fields, rawResetFields, parentFields, get, inc, ite_false,
          RawExpr.resolve, Expr.subst]
        rfl
  have bindParent : Step ⟨.letE counterType parent.val (.record resetCounterLabels methods), s⟩
      ⟨.record resetCounterLabels (parentFields address), s⟩ := by
    rw [← unpack]
    exact .letValue parent.property
  exact .head enter (.head call (.head (.letStep (counterClass_step address s))
    (.head bindParent (reuse_projections address s))))

private theorem representation_cell (address : Loc) (s : Store) :
    Step ⟨(representedCell address).resolve [], s⟩ ⟨.loc address, s⟩ :=
  .projectValue (labels := labelsP) 0 (fun _ => .loc address)

/-- The inherited getter reads the location in the supplied representation. -/
theorem reusedGet_trace (address : Loc) (n : Int) :
    Steps ⟨.app (.project (resetObject address).val "get") .skip, cellStore address n⟩
      ⟨.int n, cellStore address n⟩ :=
  .head (.appLeft (.projectValue (labels := resetCounterLabels) 0 (reusedFields_ready address)))
    (.head (.appFun .skip) (.head (.derefStep (representation_cell address _))
      (.single (.derefValue (cell_read address n)))))

theorem reusedInc_trace (address : Loc) (n : Int) :
    Steps ⟨.app (.project (resetObject address).val "inc") .skip, cellStore address n⟩
      ⟨.skip, cellStore address (1 + n)⟩ :=
  .head (.appLeft (.projectValue (labels := resetCounterLabels) 1 (reusedFields_ready address)))
    (.head (.appFun .skip) (.head (.assignLeft (representation_cell address _))
      (.head (.assignRight (.binaryRight (.int 1) (.derefStep (representation_cell address _))))
        (increment_cell address n))))

theorem reset_trace (address : Loc) (n : Int) :
    Steps ⟨.app (.project (resetObject address).val "reset") .skip, cellStore address n⟩
      ⟨.skip, cellStore address 0⟩ :=
  .head (.appLeft (.projectValue (labels := resetCounterLabels) 2 (reusedFields_ready address)))
    (.head (.appFun .skip) (.head (.assignLeft (representation_cell address _))
      (.single (cell_write address n 0))))

end Silmaril.Courses.Cambridge.Subtyping.Examples.Objects

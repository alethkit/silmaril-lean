module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Infinite.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture
open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics (Diverges Env)
open LetCase.LocallyNameless (Tm)
open Morphism.CaseSSA (erase)

universe u
variable {F Base α : Type u} {n : Nat} {β : BoundCtx (Ty Base) n}

private theorem embedTerm_eval (prim : F → Value α → Part (Value α)) (slots : Env α)
    {m : Nat} (a : Tm Empty F m) {env : Env α} {value : Value α} {start finish : Unit} :
    LambdaSSA.Semantics.Tm.Eval (instr (partPrimitives (β := β) prim slots)) env
        (erase (embedTerm a)) start value finish ↔
      LambdaSSA.Semantics.Tm.Eval (instr prim) env (erase a) start value finish := by
  induction a generalizing env value start finish with
  | fv name => exact name.elim
  | bv => constructor <;> intro run <;> cases run <;> exact .var
  | unit => constructor <;> intro run <;> cases run <;> exact .unit
  | op f a ih =>
      constructor <;> intro run <;> cases run with
      | op arg called => first | exact .op (ih.mp arg) called | exact .op (ih.mpr arg) called
  | let₁ a b iha ihb =>
      constructor <;> intro run <;> cases run with
      | let₁ arg body => first | exact .let₁ (iha.mp arg) (ihb.mp body) | exact .let₁ (iha.mpr arg) (ihb.mpr body)
  | pair a b iha ihb =>
      constructor <;> intro run <;> cases run with
      | pair left right => first | exact .pair (iha.mp left) (ihb.mp right) | exact .pair (iha.mpr left) (ihb.mpr right)
  | let₂ a b iha ihb =>
      constructor <;> intro run <;> cases run with
      | let₂ arg body => first | exact .let₂ (iha.mp arg) (ihb.mp body) | exact .let₂ (iha.mpr arg) (ihb.mpr body)
  | inl a ih =>
      constructor <;> intro run <;> cases run with
      | inl inner => first | exact .inl (ih.mp inner) | exact .inl (ih.mpr inner)
  | inr a ih =>
      constructor <;> intro run <;> cases run with
      | inr inner => first | exact .inr (ih.mp inner) | exact .inr (ih.mpr inner)
  | case a l r iha ihl ihr =>
      constructor <;> intro run <;> cases run with
      | case_inl discr branch =>
          first | exact .case_inl (iha.mp discr) (ihl.mp branch) | exact .case_inl (iha.mpr discr) (ihl.mpr branch)
      | case_inr discr branch =>
          first | exact .case_inr (iha.mp discr) (ihr.mp branch) | exact .case_inr (iha.mpr discr) (ihr.mpr branch)
  | abort => constructor <;> intro run <;> cases run

private theorem embedFlat_eval (prim : F → Value α → Part (Value α)) (slots : Env α)
    {labels m : Nat} (r : Flat F labels m) {env : Env α}
    {out : Nat} {value : Value α} {start finish : Unit} :
    LambdaSSA.Semantics.Region.Eval (instr (partPrimitives (β := β) prim slots)) env
        (embedFlat r).erase start out value finish ↔
      LambdaSSA.Semantics.Region.Eval (instr prim) env r.erase start out value finish := by
  induction r generalizing env out value start finish with
  | br i a =>
      constructor <;> intro run <;> cases run with
      | br h => first
        | exact .br ((embedTerm_eval prim slots (β := β) a).mp h)
        | exact .br ((embedTerm_eval prim slots (β := β) a).mpr h)
  | let₁ a b ih =>
      constructor <;> intro run <;> cases run with
      | let₁ h tail => first
        | exact .let₁ ((embedTerm_eval prim slots (β := β) a).mp h) (ih.mp tail)
        | exact .let₁ ((embedTerm_eval prim slots (β := β) a).mpr h) (ih.mpr tail)
  | let₂ a b ih =>
      constructor <;> intro run <;> cases run with
      | let₂ h tail => first
        | exact .let₂ ((embedTerm_eval prim slots (β := β) a).mp h) (ih.mp tail)
        | exact .let₂ ((embedTerm_eval prim slots (β := β) a).mpr h) (ih.mpr tail)
  | case a l r ihl ihr =>
      constructor <;> intro run <;> cases run with
      | case_inl h branch => first
        | exact .case_inl ((embedTerm_eval prim slots (β := β) a).mp h) (ihl.mp branch)
        | exact .case_inl ((embedTerm_eval prim slots (β := β) a).mpr h) (ihl.mpr branch)
      | case_inr h branch => first
        | exact .case_inr ((embedTerm_eval prim slots (β := β) a).mp h) (ihr.mp branch)
        | exact .case_inr ((embedTerm_eval prim slots (β := β) a).mpr h) (ihr.mpr branch)

private theorem follow_map {G H : Type u}
    {operation : G → Value α → Unit → Value α → Unit → Prop}
    {operation' : H → Value α → Unit → Value α → Unit → Prop}
    {blocks : Nat} {code : Fin blocks → LambdaSSA.Region G}
    {code' : Fin blocks → LambdaSSA.Region H} {env : Env α}
    (step : ∀ i current start out value finish,
      LambdaSSA.Semantics.Region.Eval operation (LambdaSSA.Semantics.extend env current)
        (code i) start out value finish →
      LambdaSSA.Semantics.Region.Eval operation' (LambdaSSA.Semantics.extend env current)
        (code' i) start out value finish)
    {label out : Nat} {current value : Value α} {start finish : Unit}
    (run : LambdaSSA.Semantics.Region.Follow operation env code label current start out value finish) :
    LambdaSSA.Semantics.Region.Follow operation' env code' label current start out value finish := by
  induction run using LambdaSSA.Semantics.Region.Follow.rec
      (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | exit outside => exact .exit outside
  | step inside head _ _ tail => exact .step inside (step _ _ _ _ _ _ head) (tail step)
  | _ => trivial

private theorem embed_follow (prim : F → Value α → Part (Value α)) (slots : Env α)
    {blocks exits m : Nat} (g : FiniteCFG F blocks exits m) {env : Env α}
    {label out : Nat} {current value : Value α} {start finish : Unit} :
    LambdaSSA.Semantics.Region.Follow (instr (partPrimitives (β := β) prim slots)) env
        (fun i => ((embed g).block i).erase) label current start out value finish ↔
      LambdaSSA.Semantics.Region.Follow (instr prim) env
        (fun i => (g.block i).erase) label current start out value finish :=
  ⟨follow_map (fun i _ _ _ _ _ ran => (embedFlat_eval prim slots (g.block i)).mp ran),
    follow_map (fun i _ _ _ _ _ ran => (embedFlat_eval prim slots (g.block i)).mpr ran)⟩

theorem embed_eval (prim : F → Value α → Part (Value α)) (slots : Env α)
    {blocks exits m : Nat} (g : FiniteCFG F blocks exits m) {env : Env α}
    {out : Nat} {value : Value α} {start finish : Unit} :
    LambdaSSA.Semantics.Region.Eval (instr (partPrimitives (β := β) prim slots)) env
        (embed g).erase start out value finish ↔
      LambdaSSA.Semantics.Region.Eval (instr prim) env g.erase start out value finish := by
  constructor <;> intro run <;> cases run with
  | cfg entered follow => first
    | exact .cfg ((embedFlat_eval prim slots g.entry).mp entered) ((embed_follow prim slots g).mp follow)
    | exact .cfg ((embedFlat_eval prim slots g.entry).mpr entered) ((embed_follow prim slots g).mpr follow)

theorem embed_diverges (prim : F → Value α → Part (Value α)) (slots : Env α)
    {blocks exits m : Nat} (g : FiniteCFG F blocks exits m) (env : Env α) :
    Diverges (instr (partPrimitives (β := β) prim slots)) (.region env (embed g).erase ()) ↔
      Diverges (instr prim) (.region env g.erase ()) :=
  flat_diverges_iff_of_eval (fun _ _ _ => embedFlat_eval prim slots g.entry)
    (fun i _ _ _ _ _ => embedFlat_eval prim slots (g.block i))

private theorem assemble_eval {G : Type u} (operation : G → Value α → Unit → Value α → Unit → Prop)
    (ambient : Env α) {m : Nat} (reads : Fin m → Tm Empty G 0) (slots : Env α)
    (pureReads : ∀ i v state, LambdaSSA.Semantics.Tm.Eval operation ambient (erase (reads i)) () v state ↔
      v = slots i.val ∧ state = ()) (value : Value α) (state : Unit) :
    LambdaSSA.Semantics.Tm.Eval operation ambient (erase (assemble m reads)) () value state ↔
      value = Capture.packEnv m slots ∧ state = () := by
  induction m generalizing slots value state with
  | zero =>
      constructor
      · intro run
        cases run
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact .unit
  | succ m ih =>
      have tail := ih (reads ∘ Fin.succ) (slots ∘ Nat.succ) (fun i => pureReads i.succ)
      constructor
      · intro run
        cases run with
        | pair left right =>
            obtain ⟨rfl, rfl⟩ := (tail _ _).mp left
            obtain ⟨rfl, rfl⟩ := (pureReads 0 _ _).mp right
            exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact .pair ((tail _ _).mpr ⟨rfl, rfl⟩) ((pureReads 0 _ _).mpr ⟨rfl, rfl⟩)

theorem packetInput_eval (prim : F → Value α → Part (Value α)) (slots ambient : Env α)
    (value : Value α) (state : Unit) :
    LambdaSSA.Semantics.Tm.Eval (instr (partPrimitives (β := β) prim slots)) ambient
        (erase (packetInput F β)) () value state ↔
      value = Capture.packEnv n slots ∧ state = () := by
  apply assemble_eval
  intro i v finish
  cases finish
  constructor
  · intro run
    cases run with
    | op arg returned =>
        cases arg
        exact ⟨Part.mem_some_iff.mp returned, rfl⟩
  · rintro ⟨rfl, _⟩
    exact .op .unit (Part.mem_some _)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture

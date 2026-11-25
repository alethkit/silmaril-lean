module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Categorical.Agreement
public import Silmaril.SSA.Isotope.LetIter.Categorical.AbortSequence.Thms

open Silmaril Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless

/-!
Encode each exact result as a tagged value and compare both derivations
with a single evaluation of the raw term. For iteration, pure uniformity
transports the loop along the state encoding.
-/

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.KleisliProofs

section Erasure

universe u v w q r
variable {α : Type u} (F : α → Type (max u v))

inductive Value where
  | atom (a : α) (x : F a)
  | unit
  | pair (x y : Value)
  | inl (x : Value)
  | inr (y : Value)

def encode : (A : Ty α) → Ty.denote F A → Value F
  | .base a, x => .atom a x
  | .unit, _ => .unit
  | .empty, x => x.elim
  | .product A B, (x, y) => .pair (encode A x) (encode B y)
  | .coprod A _, .inl x => .inl (encode A x)
  | .coprod _ B, .inr y => .inr (encode B y)

variable [DecidableEq α]

def decode : (A : Ty α) → Value F → Option (Ty.denote F A)
  | .base a, .atom b x => if h : b = a then some (h ▸ x) else none
  | .unit, .unit => some PUnit.unit
  | .product A B, .pair x y => (decode A x).bind fun a => (decode B y).map (Prod.mk a)
  | .coprod A _, .inl x => (decode A x).map Sum.inl
  | .coprod _ B, .inr y => (decode B y).map Sum.inr
  | _, _ => none

@[simp] theorem decode_encode (A : Ty α) (x : Ty.denote F A) :
    decode F A (encode F A x) = some x := by
  induction A with
  | base a => simp [encode, decode]
  | unit => cases x; rfl
  | empty => exact x.elim
  | product A B iha ihb =>
    cases x
    simp [encode, decode, iha, ihb]
    rfl
  | coprod A B iha ihb =>
    cases x with
    | inl x =>
      simp [encode, decode, iha]
      rfl
    | inr y =>
      simp [encode, decode, ihb]
      rfl

variable {m : Type (max u v) → Type (max u v)} [Monad m] [LawfulMonad m]

theorem encode_map_injective (A : Ty α) :
    Function.Injective (fun t : m (Ty.denote F A) => encode F A <$> t) := by
  intro x y he
  let k (v : Value F) : m (Ty.denote F A) := (decode F A v).elim x pure
  have hk (z : m (Ty.denote F A)) : (encode F A <$> z) >>= k = z := by
    rw [bind_map_left]
    have h : k ∘ encode F A = pure := by
      funext a
      simp [k]
    change z >>= (k ∘ encode F A) = z
    rw [h, bind_pure]
  change encode F A <$> x = encode F A <$> y at he
  exact (hk x).symm.trans ((congrArg (fun t => t >>= k) he).trans (hk y))

section Iteration
universe s
variable {m' : Type s → Type s} [Monad m'] [LawfulMonad m'] [Iterate m'] [LawfulElgotMonad m']

/-- Transfer a loop from typed state and result to their encoded counterparts. -/
theorem iter_map_result {A B X Y : Type s}
    (ea : A → X) (eb : B → Y)
    (f : A → m' (B ⊕ A)) (g : X → m' (Y ⊕ X))
    (hsq : ∀ a, g (ea a) = Sum.map eb ea <$> f a) (a : A) :
    eb <$> iter f a = iter g (ea a) := by
  have sq : (mapReturn f (pure ∘ eb) >=> liftPure (Sum.map id ea)) = (liftPure ea >=> g) := by
    funext z
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, hsq, mapReturn, bind_assoc]
    rw [map_eq_pure_bind]
    apply bind_congr
    intro s
    cases s <;> simp
  have hu := congrFun (LawfulElgotMonad.uniformity _ _ _ sq) a
  have hn := congrFun (LawfulElgotMonad.naturality f (pure ∘ eb)) a
  simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] at hn hu
  exact (map_eq_pure_bind eb _).trans (hn.trans hu)

end Iteration

variable [Iterate m]
variable {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ (Ty α)]
variable (M : Isotope.Semantics.InstructionModel (Ty.denote F) Φ m)

def eraseFree {Γ : Ctx ν (Ty α)} (γ : FreeEnv (Ty.denote F) Γ) (x : ν) : Value F :=
  match h : Γ.lookup x with
  | some A => encode F A (γ x A h)
  | none => .unit

omit [DecidableEq α] in
@[simp] theorem eraseFree_lookup {Γ : Ctx ν (Ty α)} (γ : FreeEnv (Ty.denote F) Γ)
    (x : ν) {A : Ty α} (h : Γ.lookup x = some A) :
    eraseFree F γ x = encode F A (γ x A h) := by
  unfold eraseFree
  split
  · rename_i B eq
    have e := Option.some.inj (eq.symm.trans h)
    subst B
    rfl
  · rename_i eq
    rw [h] at eq
    cases eq

def eraseBound {n : Nat} {β : BoundCtx (Ty α) n} (ρ : BoundEnv (Ty.denote F) β) :
    Fin n → Value F := fun i => encode F (β.get i) (ρ i)

omit [DecidableEq α] in
theorem eraseBound_snoc {n : Nat} {β : BoundCtx (Ty α) n} {A : Ty α}
    (ρ : BoundEnv (Ty.denote F) β) (a : Ty.denote F A) :
    eraseBound F (ρ.snoc a) = Fin.cases (encode F A a) (eraseBound F ρ) := by
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

def readOp (f : Φ) (x : Value F) : m (Value F) :=
  match decode F (instrSrc f) x with
  | some a => encode F (instrTrg f) <$> M.eval f a
  | none => pure .unit

def split (k : Value F → Value F → m (Value F)) : Value F → m (Value F)
  | .pair x y => k x y
  | _ => pure .unit

def branch (l r : Value F → m (Value F)) : Value F → m (Value F)
  | .inl x => l x
  | .inr y => r y
  | _ => pure .unit

def loopStep : Value F → Value F ⊕ Value F
  | .inl x => .inl x
  | .inr y => .inr y
  | _ => .inl .unit

def eval (γ : ν → Value F) : {n : Nat} → Tm ν Φ n → (Fin n → Value F) → m (Value F)
  | _, .fv x, _ => pure (γ x)
  | _, .bv i, ρ => pure (ρ i)
  | _, .op f a, ρ => eval γ a ρ >>= readOp F M f
  | _, .let₁ a b, ρ => eval γ a ρ >>= fun x => eval γ b (Fin.cases x ρ)
  | _, .unit, _ => pure .unit
  | _, .pair a b, ρ => eval γ a ρ >>= fun x => Value.pair x <$> eval γ b ρ
  | _, .let₂ a c, ρ =>
      eval γ a ρ >>= split F (fun x y => eval γ c (Fin.cases y (Fin.cases x ρ)))
  | _, .inl a, ρ => Value.inl <$> eval γ a ρ
  | _, .inr b, ρ => Value.inr <$> eval γ b ρ
  | _, .case a l r, ρ =>
      eval γ a ρ >>= branch F (fun x => eval γ l (Fin.cases x ρ)) (fun y => eval γ r (Fin.cases y ρ))
  | _, .abort a, ρ => eval γ a ρ >>= fun _ => pure .unit
  | _, .iter a b, ρ =>
      eval γ a ρ >>= iter (fun x => loopStep F <$> eval γ b (Fin.cases x ρ))

variable [LawfulElgotMonad m]

/-- The erased interpretation agrees with every data-valued typing derivation
after tagging its result. Erasure retains monadic effects, including iteration. -/
theorem eval_encode {Γ : Ctx ν (Ty α)} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : Tm ν Φ n} {A : Ty α} (d : Derivation Φ Γ β t A)
    (γ : FreeEnv (Ty.denote F) Γ) (ρ : BoundEnv (Ty.denote F) β) :
    encode F A <$> d.denote (Ty.denote F) M γ ρ =
      eval F M (eraseFree F γ) t (eraseBound F ρ) := by
  induction d with
  | fv h => simp [Derivation.denote, eval, h]
  | bv => simp [Derivation.denote, eval, eraseBound]
  | @op n β f a da ih =>
    simp only [Derivation.denote, eval, ← ih ρ, map_bind, bind_map_left]
    apply bind_congr
    intro x
    simp [readOp]
  | let₁ da db iha ihb =>
    simp only [Derivation.denote, eval, ← iha ρ, map_bind, bind_map_left]
    apply bind_congr
    intro x
    rw [ihb, eraseBound_snoc]
  | unit => simp [Derivation.denote, eval, encode]
  | @pair n β a b A B da db iha ihb =>
    simp only [Derivation.denote, eval, ← iha ρ, ← ihb ρ, map_bind, bind_map_left]
    apply bind_congr
    intro x
    simp only [map_pure, Functor.map_map]
    rw [map_eq_pure_bind]
    rfl
  | @let₂ n β a c A B C da dc iha ihc =>
    simp only [Derivation.denote, eval, ← iha ρ, map_bind, bind_map_left]
    apply bind_congr
    intro z
    rcases z with ⟨a, b⟩
    change (encode F C <$> dc.denote (Ty.denote F) M γ ((ρ.snoc a).snoc b)) =
      eval F M (eraseFree F γ) c (Fin.cases (encode F B b) (Fin.cases (encode F A a) (eraseBound F ρ)))
    rw [ihc, eraseBound_snoc, eraseBound_snoc]
  | @inl n β a A B da ih =>
    simp only [Derivation.denote, eval, ← ih ρ, map_bind, map_pure, Functor.map_map]
    rw [map_eq_pure_bind]
    rfl
  | @inr n β b A B db ih =>
    simp only [Derivation.denote, eval, ← ih ρ, map_bind, map_pure, Functor.map_map]
    rw [map_eq_pure_bind]
    rfl
  | @case n β a l r A B C da dl dr iha ihl ihr =>
    simp only [Derivation.denote, eval, ← iha ρ, map_bind, bind_map_left]
    apply bind_congr
    intro z
    cases z with
    | inl x =>
      change (encode F C <$> dl.denote (Ty.denote F) M γ (ρ.snoc x)) =
        eval F M (eraseFree F γ) l (Fin.cases (encode F A x) (eraseBound F ρ))
      rw [ihl, eraseBound_snoc]
    | inr y =>
      change (encode F C <$> dr.denote (Ty.denote F) M γ (ρ.snoc y)) =
        eval F M (eraseFree F γ) r (Fin.cases (encode F B y) (eraseBound F ρ))
      rw [ihr, eraseBound_snoc]
  | abort da ih =>
    simp only [Derivation.denote, eval, ← ih ρ, map_bind, bind_map_left]
    apply bind_congr
    intro x
    exact x.elim
  | @iter n β a b A B da db iha ihb =>
    simp only [Derivation.denote, eval, ← iha ρ, map_bind, bind_map_left]
    apply bind_congr
    intro x
    let f (a : Ty.denote F A) : m (Ty.denote F B ⊕ Ty.denote F A) :=
      db.denote (Ty.denote F) M γ (ρ.snoc a)
    let g (x : Value F) : m (Value F ⊕ Value F) :=
      loopStep F <$> eval F M (eraseFree F γ) b (Fin.cases x (eraseBound F ρ))
    have hf : (fun a => f a >>= pure) = f := funext fun a => bind_pure (f a)
    change (encode F B <$> iter (fun a => f a >>= pure) x) = iter g (encode F A x)
    rw [hf]
    apply iter_map_result (encode F A) (encode F B) f g
    intro a
    have ih := ihb (ρ.snoc a)
    rw [eraseBound_snoc] at ih
    change loopStep F <$> eval F M (eraseFree F γ) b (Fin.cases (encode F A a) (eraseBound F ρ)) = _
    rw [← ih, Functor.map_map]
    congr 1
    funext s
    cases s <;> rfl

theorem denote_coherent {Γ : Ctx ν (Ty α)} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : Tm ν Φ n} {A : Ty α} (d e : Derivation Φ Γ β t A)
    (γ : FreeEnv (Ty.denote F) Γ) (ρ : BoundEnv (Ty.denote F) β) :
    d.denote (Ty.denote F) M γ ρ = e.denote (Ty.denote F) M γ ρ :=
  encode_map_injective F A ((eval_encode F M d γ ρ).trans (eval_encode F M e γ ρ).symm)


end Erasure

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w q r

variable {α : Type u} [DecidableEq α] (F : α → Type (max u v))
  {m : Type (max u v) → Type (max u v)} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {Φ : Type q} [HasTy Φ (Ty α)] (M : Isotope.Semantics.InstructionModel (Ty.denote F) Φ m)
  {ν : Type w} [DecidableEq ν]

local notation "Jm" => Kleisli.Adjunction.toKleisli (ofTypeMonad m)
local notation "TmD" => ofTypeModel (Ty.denote F)

public theorem typingCoherent_ofType :
    letI := ofInstructionModel (Ty.denote F) M
    TypingCoherent (ν := ν) Jm TmD Φ := by
  let inst := ofInstructionModel (Ty.denote F) M
  intro Γ n β t A d e
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  funext z
  obtain ⟨γ, ρ⟩ := z
  change (denoteOfType (Ty.denote F) M d).of (γ, ρ) = (denoteOfType (Ty.denote F) M e).of (γ, ρ)
  exact (denoteOfType_eq _ _ d γ ρ).trans
    ((denote_coherent F M d e _ _).trans (denoteOfType_eq _ _ e γ ρ).symm)

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- Soundness for every native AbortEquiv derivation in the set-valued Kleisli interpretation. -/
public theorem denoteOfType_eq_of_abortEquiv {Γ : Ctx ν (Ty α)} {n : Nat} {β : BoundCtx (Ty α) n}
    {a b : Tm ν Φ n} {A : Ty α}
    (pureM : Isotope.Semantics.InstructionModel.RespectsPure (ε := ε) M)
    (h : AbortEquiv (⊥ : ε) Γ β a b A)
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    denoteOfType (Ty.denote F) M da = denoteOfType (Ty.denote F) M db := by
  let inst := ofInstructionModel (Ty.denote F) M
  apply denote_abortEquiv_of_coherent_shared_tensor Jm TmD (typingCoherent_ofType F M) _ _ h da db
  · intro R S
    exact ⟨rfl, rfl⟩
  · intro f hf
    obtain ⟨g, hg⟩ := pureM f hf
    refine ⟨TypeCat.ofHom g, ?_⟩
    apply Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    funext x
    exact hg x

omit [DecidableEq α] in
theorem boundEnv_surjective {n : Nat} (β : BoundCtx (Ty α) n) :
    Function.Surjective (boundEnv (Ty.denote F) (β := β)) := by
  induction β with
  | nil =>
    intro ρ
    exact ⟨PUnit.unit, funext (fun i => i.elim0)⟩
  | snoc β A ih =>
    intro ρ
    obtain ⟨x, hx⟩ := ih (fun i => ρ i.succ)
    refine ⟨(x, ρ 0), ?_⟩
    refine (boundEnv_snoc (Ty.denote F) (β := β) (A := A) x (ρ 0)).trans ?_
    refine (congrArg (fun env => BoundEnv.snoc (A := A) env (ρ 0)) hx).trans ?_
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- Direct monadic soundness for all bound environments and an empty free context. -/
public theorem denote_eq_of_abortEquiv_nil {n : Nat} {β : BoundCtx (Ty α) n}
    {a b : Tm Empty Φ n} {A : Ty α}
    (pureM : Isotope.Semantics.InstructionModel.RespectsPure (ε := ε) M)
    (h : AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) β a b A)
    (da : Derivation Φ .nil β a A) (db : Derivation Φ .nil β b A)
    (ρ : BoundEnv (Ty.denote F) β) :
    da.denote (Ty.denote F) M (fun x => x.elim) ρ =
      db.denote (Ty.denote F) M (fun x => x.elim) ρ := by
  obtain ⟨packed, rfl⟩ := boundEnv_surjective F β ρ
  have he := denoteOfType_eq_of_abortEquiv F M pureM h da db
  let c : ctxObj TmD (.nil : Ctx Empty (Ty α)) := PUnit.unit
  have hp := congrArg (fun f => f.of (c, packed)) he
  have hmono := (denoteOfType_eq _ _ da c packed).symm.trans
    (hp.trans (denoteOfType_eq _ _ db c packed))
  have hf : freeEnv (Ty.denote F) (Γ := (.nil : Ctx Empty (Ty α))) c =
      (fun x => x.elim) := by
    funext x
    exact x.elim
  change da.denote (Ty.denote F) M (freeEnv (Ty.denote F) c) (boundEnv (Ty.denote F) packed) =
    db.denote (Ty.denote F) M (freeEnv (Ty.denote F) c) (boundEnv (Ty.denote F) packed) at hmono
  rwa [hf] at hmono

end Silmaril.Isotope.LetIter.Semantics.Categorical.KleisliProofs

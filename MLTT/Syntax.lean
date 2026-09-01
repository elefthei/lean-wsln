import WSLN

/-!
# Syntax of Martin-Löf type theory

Port of `agda-code/agda/MLTT/Syntax.agda`.

Agda's pattern synonyms become `@[match_pattern] def`s with ASCII names plus scoped
bold-unicode notation, so both `Pi' l l' A B` and `𝚷 l l' A B` work, and both can be
matched on.  `𝐍𝐚𝐭`/`𝐳𝐞𝐫𝐨`/`𝐬𝐮𝐜𝐜`/`𝐫𝐞𝐟𝐥` are named `Nat'`/`zero'`/`succ'`/`refl'`
to avoid shadowing Lean's `Nat`, `Nat.zero`, `Nat.succ` and `Eq.refl`.
-/

namespace MLTT

open WSLN

/-! ## Universe levels -/

/-- Agda: `Lvl` (MLTT/Syntax.agda). -/
abbrev Lvl := Nat

/-! ## Signature for types and terms -/

/-- Agda: `OpMLTT` (MLTT/Syntax.agda). -/
inductive Op where
  /-- Agda: `′Univ′`. Universe type. -/
  | univ (l : Lvl) : Op
  /-- Agda: `′Pi′`. Dependent function type. -/
  | pi (l l' : Lvl) : Op
  /-- Agda: `′lam′`. Function abstraction. -/
  | lam : Op
  /-- Agda: `′app′`. Function application. -/
  | app : Op
  /-- Agda: `′Id′`. Identity type. -/
  | Id : Op
  /-- Agda: `′refl′`. Reflexivity proof. -/
  | refl : Op
  /-- Agda: `′J′`. Identity elimination. -/
  | J : Op
  /-- Agda: `′Nat′`. Natural number type. -/
  | nat : Op
  /-- Agda: `′zero′`. Zero. -/
  | zero : Op
  /-- Agda: `′succ′`. Successor. -/
  | succ : Op
  /-- Agda: `′natrec′`. Natural number elimination. -/
  | natrec : Op
  deriving DecidableEq

/-- Agda: `arMLTT` (MLTT/Syntax.agda). -/
def ar : Op → List Nat
  | .univ _ => []
  | .pi _ _ => [0, 1]
  | .lam => [0, 1]
  | .app => [0, 0, 1, 0]
  | .Id => [0, 0, 0]
  | .refl => [0]
  | .J => [2, 0, 0, 0, 0]
  | .nat => []
  | .zero => []
  | .succ => [0]
  | .natrec => [1, 0, 2, 0]

/-- Agda: `MLTT : Sig` (MLTT/Syntax.agda). -/
def sig : Sig := ⟨Op, ar⟩

instance : DecidableEq sig.Op := inferInstanceAs (DecidableEq Op)

/-! ## Terms of Martin-Löf type theory -/

/-- Agda: `Tm[_]` (MLTT/Syntax.agda). -/
abbrev Tm (n : Nat) := WSLN.Trm sig n

/-- Agda: `Tm` (MLTT/Syntax.agda). -/
abbrev Tm0 := Tm 0

/-- Agda: `Ty[_]` (MLTT/Syntax.agda). Types are particular kinds of term. -/
abbrev Ty (n : Nat) := Tm n

/-- Agda: `Ty` (MLTT/Syntax.agda). -/
abbrev Ty0 := Ty 0

/-! ## Notation -/

/-- Agda: `pattern 𝐯 x = 𝐚 x` (MLTT/Syntax.agda). -/
@[match_pattern] def vr {n : Nat} (x : Atom) : Tm n := .atom x

/-- Agda: `pattern 𝐔 l` (MLTT/Syntax.agda). -/
@[match_pattern] def U {n : Nat} (l : Lvl) : Ty n := .op (.univ l) .nil

/-- Agda: `pattern 𝚷 l l' A B` (MLTT/Syntax.agda). -/
@[match_pattern] def Pi' {n : Nat} (l l' : Lvl) (A : Ty n) (B : Ty (n + 1)) : Ty n :=
  .op (.pi l l') (.cons A (.cons B .nil))

/-- Agda: `pattern 𝛌 A f` (MLTT/Syntax.agda). -/
@[match_pattern] def lam {n : Nat} (A : Ty n) (f : Tm (n + 1)) : Tm n :=
  .op .lam (.cons A (.cons f .nil))

/-- Agda: `pattern _∙[_,_]_ b A B a` (MLTT/Syntax.agda). -/
@[match_pattern] def app {n : Nat} (b : Tm n) (A : Ty n) (B : Ty (n + 1)) (a : Tm n) :
    Tm n := .op .app (.cons b (.cons A (.cons B (.cons a .nil))))

/-- Agda: `pattern 𝐈𝐝 A a a'` (MLTT/Syntax.agda). -/
@[match_pattern] def Id {n : Nat} (A : Ty n) (a a' : Tm n) : Ty n :=
  .op .Id (.cons A (.cons a (.cons a' .nil)))

/-- Agda: `pattern 𝐫𝐞𝐟𝐥 a` (MLTT/Syntax.agda). -/
@[match_pattern] def refl' {n : Nat} (a : Tm n) : Tm n := .op .refl (.cons a .nil)

/-- Agda: `pattern 𝐉 C a b c e` (MLTT/Syntax.agda). -/
@[match_pattern] def J {n : Nat} (C : Ty (n + 2)) (a b c e : Tm n) : Tm n :=
  .op .J (.cons C (.cons a (.cons b (.cons c (.cons e .nil)))))

/-- Agda: `pattern 𝐍𝐚𝐭` (MLTT/Syntax.agda). -/
@[match_pattern] def Nat' {n : Nat} : Ty n := .op .nat .nil

/-- Agda: `pattern 𝐳𝐞𝐫𝐨` (MLTT/Syntax.agda). -/
@[match_pattern] def zero' {n : Nat} : Tm n := .op .zero .nil

/-- Agda: `pattern 𝐬𝐮𝐜𝐜 a` (MLTT/Syntax.agda). -/
@[match_pattern] def succ' {n : Nat} (a : Tm n) : Tm n := .op .succ (.cons a .nil)

/-- Agda: `pattern 𝐧𝐫𝐞𝐜 C c₀ cs a` (MLTT/Syntax.agda). -/
@[match_pattern] def nrec {n : Nat} (C : Ty (n + 1)) (c₀ : Tm n) (cs : Tm (n + 2))
    (a : Tm n) : Tm n := .op .natrec (.cons C (.cons c₀ (.cons cs (.cons a .nil))))

@[inherit_doc vr] scoped notation:max "𝐯" x:max => MLTT.vr x
@[inherit_doc U] scoped notation:max "𝐔 " l:max => MLTT.U l
@[inherit_doc Pi'] scoped notation:max "𝚷 " l:max l':max A:max B:max =>
  MLTT.Pi' l l' A B
@[inherit_doc lam] scoped notation:max "𝛌 " A:max f:max => MLTT.lam A f
@[inherit_doc app] scoped notation:70 b:71 " ∙[ " A ", " B " ] " a:71 =>
  MLTT.app b A B a
@[inherit_doc Id] scoped notation:max "𝐈𝐝 " A:max a:max a':max => MLTT.Id A a a'
@[inherit_doc refl'] scoped notation:max "𝐫𝐞𝐟𝐥 " a:max => MLTT.refl' a
@[inherit_doc J] scoped notation:max "𝐉 " C:max a:max b:max c:max e:max =>
  MLTT.J C a b c e
@[inherit_doc Nat'] scoped notation:max "𝐍𝐚𝐭" => MLTT.Nat'
@[inherit_doc zero'] scoped notation:max "𝐳𝐞𝐫𝐨" => MLTT.zero'
@[inherit_doc succ'] scoped notation:max "𝐬𝐮𝐜𝐜 " a:max => MLTT.succ' a
@[inherit_doc nrec] scoped notation:max "𝐧𝐫𝐞𝐜 " C:max c₀:max cs:max a:max =>
  MLTT.nrec C c₀ cs a

/-! ## Definitional equations for the action on the pattern constructors

Agda gets these for free from its pattern synonyms.  In Lean they are shared plumbing
used by `MLTT/Substitution.lean`, `MLTT/Admissible.lean` and `MLTT/ExistsFresh.lean`,
and are deliberately kept out of the global simp set. -/

theorem sbApp {n : Nat} (σ : Sb sig) (b : Tm n) (A : Ty n) (B : Ty (n + 1))
    (a : Tm n) : σ * (b ∙[ A, B ] a) = (σ * b) ∙[ σ * A, σ * B ] (σ * a) := rfl

theorem sbId {n : Nat} (σ : Sb sig) (A : Ty n) (a a' : Tm n) :
    σ * (𝐈𝐝 A a a') = 𝐈𝐝 (σ * A) (σ * a) (σ * a') := rfl

theorem sbSucc {n : Nat} (σ : Sb sig) (a : Tm n) :
    σ * (𝐬𝐮𝐜𝐜 a) = 𝐬𝐮𝐜𝐜 (σ * a) := rfl

theorem sbAtom (σ : Sb sig) (x : Atom) : σ * (𝐯x : Tm0) = σ x := by simp [vr]

/-! ## Contexts -/

/-- Agda: `Cx` (MLTT/Syntax.agda). -/
inductive Cx : Type where
  /-- Agda: `◇`. -/
  | nil : Cx
  /-- Agda: `_⨟_∶_⦂_`. -/
  | snoc (Γ : Cx) (x : Atom) (A : Ty0) (l : Lvl) : Cx

@[inherit_doc Cx.nil] scoped notation "◇" => MLTT.Cx.nil
@[inherit_doc Cx.snoc]
scoped notation:40 Γ:40 " ⨟ " x:41 " ∶ " A:41 " ⦂ " l:41 => MLTT.Cx.snoc Γ x A l

/-- Agda: `dom` (MLTT/Syntax.agda). The domain of a context. -/
def dom : Cx → Fset
  | .nil => ∅
  | .snoc Γ x _ _ => dom Γ ∪ ｛ x ｝

/-- Agda: `FiniteSupportCx` (MLTT/Syntax.agda). Freshness for contexts. -/
instance instFiniteSupportCx : FiniteSupport Cx := ⟨dom⟩

@[simp] theorem supp_cx (Γ : Cx) : supp Γ = dom Γ := rfl

@[simp] theorem dom_nil : dom ◇ = ∅ := rfl

@[simp] theorem dom_snoc (Γ : Cx) (x : Atom) (A : Ty0) (l : Lvl) :
    dom (Γ ⨟ x ∶ A ⦂ l) = dom Γ ∪ ｛ x ｝ := rfl

/-- Agda: `cx⁻¹` (MLTT/Syntax.agda). -/
theorem snoc_inj {Γ Γ' : Cx} {x x' : Atom} {A A' : Ty0} {l l' : Lvl}
    (e : (Γ ⨟ x ∶ A ⦂ l) = (Γ' ⨟ x' ∶ A' ⦂ l')) :
    Γ = Γ' ∧ x = x' ∧ A = A' ∧ l = l' := by
  cases e; exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Membership of contexts -/

/-- Agda: `_isIn_` (MLTT/Syntax.agda). -/
inductive IsIn : (Atom × Ty0 × Lvl) → Cx → Prop where
  /-- Agda: `isInNew`. -/
  | new {Γ : Cx} {x : Atom} {A : Ty0} {l : Lvl} : IsIn (x, A, l) (Γ ⨟ x ∶ A ⦂ l)
  /-- Agda: `isInOld`. -/
  | old {xAl : Atom × Ty0 × Lvl} {Γ : Cx} {x' : Atom} {A' : Ty0} {l' : Lvl}
      (p : IsIn xAl Γ) : IsIn xAl (Γ ⨟ x' ∶ A' ⦂ l')

@[inherit_doc IsIn] scoped infix:40 " isIn " => MLTT.IsIn

/-- Agda: `isIn→dom` (MLTT/Syntax.agda), stated on the raw triple so that
`induction` applies. -/
theorem IsIn.dom_mem {Γ : Cx} {xAl : Atom × Ty0 × Lvl} (h : IsIn xAl Γ) :
    xAl.1 ∈ dom Γ := by
  induction h with
  | new => exact .unionR .single
  | old _ ih => exact .unionL ih

/-- Agda: `isIn→dom` (MLTT/Syntax.agda). -/
theorem isIn_dom {Γ : Cx} {x : Atom} {A : Ty0} {l : Lvl} (h : (x, A, l) isIn Γ) :
    x ∈ dom Γ := h.dom_mem

/-- Agda: `dom→isIn` (MLTT/Syntax.agda). -/
theorem dom_isIn {Γ : Cx} {x : Atom} (h : x ∈ dom Γ) :
    ∃ (A : Ty0) (l : Lvl), (x, A, l) isIn Γ := by
  induction Γ with
  | nil => cases h
  | snoc Γ y B l' ih =>
      rw [dom_snoc] at h
      cases h with
      | unionL p =>
          obtain ⟨A, l, p'⟩ := ih p
          exact ⟨A, l, .old p'⟩
      | unionR p => cases p; exact ⟨B, l', .new⟩

end MLTT

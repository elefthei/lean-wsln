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

abbrev Lvl := Nat

/-! ## Signature for types and terms -/

inductive Op where
  /-- Universe type. -/
  | univ (l : Lvl) : Op
  /-- Dependent function type. -/
  | pi (l l' : Lvl) : Op
  /-- Function abstraction. -/
  | lam : Op
  /-- Function application. -/
  | app : Op
  /-- Identity type. -/
  | id : Op
  /-- Reflexivity proof. -/
  | refl : Op
  /-- Identity elimination. -/
  | j : Op
  /-- Natural number type. -/
  | nat : Op
  /-- Zero. -/
  | zero : Op
  /-- Successor. -/
  | succ : Op
  /-- Natural number elimination. -/
  | natrec : Op
  deriving DecidableEq

def ar : Op → List Nat
  | .univ _ => []
  | .pi _ _ => [0, 1]
  | .lam => [0, 1]
  | .app => [0, 0, 1, 0]
  | .id => [0, 0, 0]
  | .refl => [0]
  | .j => [2, 0, 0, 0, 0]
  | .nat => []
  | .zero => []
  | .succ => [0]
  | .natrec => [1, 0, 2, 0]

def sig : Sig := ⟨Op, ar⟩

instance : DecidableEq sig.Op := inferInstanceAs (DecidableEq Op)

/-! ## Terms of Martin-Löf type theory -/

abbrev Tm (n : Nat) := WSLN.Trm sig n

abbrev Tm0 := Tm 0

/-- Types are particular kinds of term. -/
abbrev Ty (n : Nat) := Tm n

abbrev Ty0 := Ty 0

/-! ## Notation -/

/-- The variable pattern: `𝐯 x` is the atom `x` as a term. -/
@[match_pattern] def vr {n : Nat} (x : Atom) : Tm n := .atom x

/-- The universe pattern `𝐔 l`. -/
@[match_pattern] def U {n : Nat} (l : Lvl) : Ty n := .op (.univ l) .nil

/-- The Π-type pattern `𝚷 l l' A B`. -/
@[match_pattern] def Pi' {n : Nat} (l l' : Lvl) (A : Ty n) (B : Ty (n + 1)) : Ty n :=
  .op (.pi l l') (.cons A (.cons B .nil))

/-- The abstraction pattern `𝛌 A f`. -/
@[match_pattern] def lam {n : Nat} (A : Ty n) (f : Tm (n + 1)) : Tm n :=
  .op .lam (.cons A (.cons f .nil))

/-- The application pattern `b ∙[ A, B ] a`. -/
@[match_pattern] def app {n : Nat} (b : Tm n) (A : Ty n) (B : Ty (n + 1)) (a : Tm n) :
    Tm n := .op .app (.cons b (.cons A (.cons B (.cons a .nil))))

/-- Named `Id'` so that it does not shadow core's `Id` under `open MLTT`, matching
`Nat'`/`Pi'`/`refl'`. -/
@[match_pattern] def Id' {n : Nat} (A : Ty n) (a a' : Tm n) : Ty n :=
  .op .id (.cons A (.cons a (.cons a' .nil)))

/-- The reflexivity pattern `𝐫𝐞𝐟𝐥 a`. -/
@[match_pattern] def refl' {n : Nat} (a : Tm n) : Tm n := .op .refl (.cons a .nil)

/-- The identity eliminator pattern `𝐉 C a b c e`. -/
@[match_pattern] def J {n : Nat} (C : Ty (n + 2)) (a b c e : Tm n) : Tm n :=
  .op .j (.cons C (.cons a (.cons b (.cons c (.cons e .nil)))))

/-- The naturals pattern `𝐍𝐚𝐭`. -/
@[match_pattern] def Nat' {n : Nat} : Ty n := .op .nat .nil

/-- The zero pattern `𝐳𝐞𝐫𝐨`. -/
@[match_pattern] def zero' {n : Nat} : Tm n := .op .zero .nil

/-- The successor pattern `𝐬𝐮𝐜𝐜 a`. -/
@[match_pattern] def succ' {n : Nat} (a : Tm n) : Tm n := .op .succ (.cons a .nil)

/-- The recursor pattern `𝐧𝐫𝐞𝐜 C c₀ cs a`. -/
@[match_pattern] def nrec {n : Nat} (C : Ty (n + 1)) (c₀ : Tm n) (cs : Tm (n + 2))
    (a : Tm n) : Tm n := .op .natrec (.cons C (.cons c₀ (.cons cs (.cons a .nil))))

@[inherit_doc vr] scoped notation:max "𝐯" x:max => MLTT.vr x
@[inherit_doc U] scoped notation:max "𝐔 " l:max => MLTT.U l
@[inherit_doc Pi'] scoped notation:max "𝚷 " l:max l':max A:max B:max =>
  MLTT.Pi' l l' A B
@[inherit_doc lam] scoped notation:max "𝛌 " A:max f:max => MLTT.lam A f
@[inherit_doc app] scoped notation:70 b:71 " ∙[ " A ", " B " ] " a:71 =>
  MLTT.app b A B a
@[inherit_doc Id'] scoped notation:max "𝐈𝐝 " A:max a:max a':max => MLTT.Id' A a a'
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

inductive Cx : Type where
  /-- The empty context. -/
  | nil : Cx
  /-- Context extension `Γ ⨟ x ∶ A ⦂ l`. -/
  | snoc (Γ : Cx) (x : Atom) (A : Ty0) (l : Lvl) : Cx

@[inherit_doc Cx.nil] scoped notation "◇" => MLTT.Cx.nil
@[inherit_doc Cx.snoc]
scoped notation:40 Γ:40 " ⨟ " x:41 " ∶ " A:41 " ⦂ " l:41 => MLTT.Cx.snoc Γ x A l

/-- The domain of a context. -/
def dom : Cx → Fset
  | .nil => ∅
  | .snoc Γ x _ _ => dom Γ ∪ ｛ x ｝

/-- Freshness for contexts. -/
instance instFiniteSupportCx : FiniteSupport Cx := ⟨dom⟩

@[simp] theorem supp_cx (Γ : Cx) : supp Γ = dom Γ := rfl

@[simp] theorem dom_nil : dom ◇ = ∅ := rfl

@[simp] theorem dom_snoc (Γ : Cx) (x : Atom) (A : Ty0) (l : Lvl) :
    dom (Γ ⨟ x ∶ A ⦂ l) = dom Γ ∪ ｛ x ｝ := rfl

theorem snoc_inj {Γ Γ' : Cx} {x x' : Atom} {A A' : Ty0} {l l' : Lvl}
    (e : (Γ ⨟ x ∶ A ⦂ l) = (Γ' ⨟ x' ∶ A' ⦂ l')) :
    Γ = Γ' ∧ x = x' ∧ A = A' ∧ l = l' := by
  cases e; exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Membership of contexts -/

/-- Context membership: the triple `(x, A, l)` occurs in `Γ`. -/
inductive IsIn : (Atom × Ty0 × Lvl) → Cx → Prop where
  | new {Γ : Cx} {x : Atom} {A : Ty0} {l : Lvl} : IsIn (x, A, l) (Γ ⨟ x ∶ A ⦂ l)
  | old {xAl : Atom × Ty0 × Lvl} {Γ : Cx} {x' : Atom} {A' : Ty0} {l' : Lvl}
      (p : IsIn xAl Γ) : IsIn xAl (Γ ⨟ x' ∶ A' ⦂ l')

@[inherit_doc IsIn] scoped infix:40 " isIn " => MLTT.IsIn

/-- Membership implies domain membership, stated on the raw triple so that `induction`
applies. -/
theorem IsIn.dom_mem {Γ : Cx} {xAl : Atom × Ty0 × Lvl} (h : IsIn xAl Γ) :
    xAl.1 ∈ dom Γ := by
  induction h with
  | new => exact .unionR .single
  | old _ ih => exact .unionL ih

theorem isIn_dom {Γ : Cx} {x : Atom} {A : Ty0} {l : Lvl} (h : (x, A, l) isIn Γ) :
    x ∈ dom Γ := h.dom_mem

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

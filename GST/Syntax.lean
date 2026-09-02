import WSLN

/-!
# Syntax of Gödel's System T

Port of `agda-code/agda/GST/Syntax.agda`.

Simple types, the binding signature of System T, and its terms in the well-scoped
locally nameless representation.

Agda's pattern synonyms become `@[match_pattern] def`s with ASCII names plus scoped
unicode notation, as in the MLTT port.  `decEqTy`/`hasDecEqTy`/`hasDecEqOpGST` are the
`deriving DecidableEq` instances; `decTrmEq` for terms is then inherited from
`WSLN/Term.lean`.

The type-decomposition deciders `𝐍𝐚𝐭?`, `⇒?` and `?⇒?` return `WSLN.Dec` of a `Sigma`,
not `Decidable` of an `Exists`: `GST/DecidableConv.lean` needs the witness
computationally.
-/

namespace GST

open WSLN

/-! ## Simple types -/

/-- Agda: `Ty` (GST/Syntax.agda). -/
inductive Ty where
  /-- Agda: `𝐍𝐚𝐭`. The type of natural numbers. -/
  | nat : Ty
  /-- Agda: `_⇒_`. Function types. -/
  | arrow (A B : Ty) : Ty
  deriving DecidableEq, Repr  -- Agda: `decEqTy` / `hasDecEqTy`

@[inherit_doc Ty.nat] scoped notation:max "𝐍𝐚𝐭" => GST.Ty.nat
@[inherit_doc Ty.arrow] scoped infixr:60 " ⇒ " => GST.Ty.arrow

/-- Agda: `⇒inj` (GST/Syntax.agda). -/
theorem arrow_inj {A A' B B' : Ty} (e : A ⇒ B = A' ⇒ B') : A = A' ∧ B = B' := by
  cases e; exact ⟨rfl, rfl⟩

/-! ## Signature for terms -/

/-- Agda: `OpGST` (GST/Syntax.agda). -/
inductive Op where
  /-- Agda: `′lam′`. Function abstraction, annotated with the domain type. -/
  | lam (A : Ty) : Op
  /-- Agda: `′app′`. Function application. -/
  | app : Op
  /-- Agda: `′zero′`. Zero. -/
  | zero : Op
  /-- Agda: `′succ′`. Successor. -/
  | succ : Op
  /-- Agda: `′natrec′`. Natural number elimination. -/
  | natrec : Op
  deriving DecidableEq  -- Agda: `hasDecEqOpGST`

/-- Agda: `arGST` (GST/Syntax.agda). -/
def ar : Op → List Nat
  | .lam _ => [1]
  | .app => [0, 0]
  | .zero => []
  | .succ => [0]
  | .natrec => [0, 0, 0]

/-- Agda: `GST : Sig` (GST/Syntax.agda). -/
def sig : Sig := ⟨Op, ar⟩

instance : DecidableEq sig.Op := inferInstanceAs (DecidableEq Op)

/-! ## Terms of Gödel's System T -/

/-- Agda: `Tm[_]` (GST/Syntax.agda). -/
abbrev Tm (n : Nat) := WSLN.Trm sig n

/-- Agda: `Tm` (GST/Syntax.agda). -/
abbrev Tm0 := Tm 0

/-! ## Notation -/

/-- Agda: `pattern 𝐯 x = 𝐚 x` (GST/Syntax.agda). -/
@[match_pattern] def vr {n : Nat} (x : Atom) : Tm n := .atom x

/-- Agda: `pattern 𝛌 A a` (GST/Syntax.agda). -/
@[match_pattern] def lam {n : Nat} (A : Ty) (b : Tm (n + 1)) : Tm n :=
  .op (.lam A) (.cons b .nil)

/-- Agda: `pattern _∙_ b a` (GST/Syntax.agda). -/
@[match_pattern] def app {n : Nat} (b a : Tm n) : Tm n :=
  .op .app (.cons b (.cons a .nil))

/-- Agda: `pattern 𝐳𝐞𝐫𝐨` (GST/Syntax.agda). -/
@[match_pattern] def zero' {n : Nat} : Tm n := .op .zero .nil

/-- Agda: `pattern 𝐬𝐮𝐜𝐜 a` (GST/Syntax.agda). -/
@[match_pattern] def succ' {n : Nat} (a : Tm n) : Tm n := .op .succ (.cons a .nil)

/-- Agda: `pattern 𝐧𝐫𝐞𝐜 c₀ cs a` (GST/Syntax.agda). -/
@[match_pattern] def nrec {n : Nat} (c₀ cs a : Tm n) : Tm n :=
  .op .natrec (.cons c₀ (.cons cs (.cons a .nil)))

@[inherit_doc vr] scoped notation:max "𝐯" x:max => GST.vr x
@[inherit_doc lam] scoped notation:max "𝛌 " A:max b:max => GST.lam A b
@[inherit_doc app] scoped infixl:70 " ∙ " => GST.app
@[inherit_doc zero'] scoped notation:max "𝐳𝐞𝐫𝐨" => GST.zero'
@[inherit_doc succ'] scoped notation:max "𝐬𝐮𝐜𝐜 " a:max => GST.succ' a
@[inherit_doc nrec] scoped notation:max "𝐧𝐫𝐞𝐜 " c₀:max cs:max a:max =>
  GST.nrec c₀ cs a

/-! ## Defining equations for the pattern constructors

Lean-only, no Agda counterpart: Agda's pattern synonyms are transparent, so support,
size, substitution and concretion compute on them definitionally.  In Lean the
pattern constructors are `def`s, so their equations are `rfl` lemmas in the default
`simp` set. -/

@[simp] theorem supp_vr {n : Nat} (x : Atom) : supp (𝐯x : Tm n) = ｛ x ｝ := rfl

@[simp] theorem supp_lam {n : Nat} (A : Ty) (b : Tm (n + 1)) :
    supp (𝛌 A b) = supp b ∪ ∅ := rfl

@[simp] theorem supp_app {n : Nat} (b a : Tm n) :
    supp (b ∙ a) = supp b ∪ (supp a ∪ ∅) := rfl

@[simp] theorem supp_zero {n : Nat} : supp (𝐳𝐞𝐫𝐨 : Tm n) = ∅ := rfl

@[simp] theorem supp_succ {n : Nat} (a : Tm n) : supp (𝐬𝐮𝐜𝐜 a) = supp a ∪ ∅ := rfl

@[simp] theorem supp_nrec {n : Nat} (c₀ cs a : Tm n) :
    supp (𝐧𝐫𝐞𝐜 c₀ cs a) = supp c₀ ∪ (supp cs ∪ (supp a ∪ ∅)) := rfl

@[simp] theorem size_vr {n : Nat} (x : Atom) : (𝐯x : Tm n).size = 0 := rfl

@[simp] theorem size_lam {n : Nat} (A : Ty) (b : Tm (n + 1)) :
    (𝛌 A b).size = max b.size 0 + 1 := rfl

@[simp] theorem size_app {n : Nat} (b a : Tm n) :
    (b ∙ a).size = max b.size (max a.size 0) + 1 := rfl

@[simp] theorem size_zero {n : Nat} : (𝐳𝐞𝐫𝐨 : Tm n).size = 1 := rfl

@[simp] theorem size_succ {n : Nat} (a : Tm n) :
    (𝐬𝐮𝐜𝐜 a).size = max a.size 0 + 1 := rfl

@[simp] theorem size_nrec {n : Nat} (c₀ cs a : Tm n) :
    (𝐧𝐫𝐞𝐜 c₀ cs a).size = max c₀.size (max cs.size (max a.size 0)) + 1 := rfl

@[simp] theorem sb_vr {n : Nat} (σ : Sb sig) (x : Atom) :
    σ * (𝐯x : Tm n) = (σ x).weaken n (Nat.zero_le n) := rfl

@[simp] theorem sb_lam {n : Nat} (σ : Sb sig) (A : Ty) (b : Tm (n + 1)) :
    σ * (𝛌 A b) = 𝛌 A (σ * b) := rfl

@[simp] theorem sb_app {n : Nat} (σ : Sb sig) (b a : Tm n) :
    σ * (b ∙ a) = (σ * b) ∙ (σ * a) := rfl

@[simp] theorem sb_zero {n : Nat} (σ : Sb sig) : σ * (𝐳𝐞𝐫𝐨 : Tm n) = 𝐳𝐞𝐫𝐨 := rfl

@[simp] theorem sb_succ {n : Nat} (σ : Sb sig) (a : Tm n) :
    σ * (𝐬𝐮𝐜𝐜 a) = 𝐬𝐮𝐜𝐜 (σ * a) := rfl

@[simp] theorem sb_nrec {n : Nat} (σ : Sb sig) (c₀ cs a : Tm n) :
    σ * (𝐧𝐫𝐞𝐜 c₀ cs a) = 𝐧𝐫𝐞𝐜 (σ * c₀) (σ * cs) (σ * a) := rfl

-- `(𝛌 A b)[u]` and `x ． 𝛌 A b` have no such equation: under a binder of depth 1 the
-- opened/closed index is shifted (`WSLN.shiftIdx`), so the body is not `b[u]` resp.
-- `x ． b`.  `GST/Admissible.lean` uses `concAbs`/`concAbs'` instead.

@[simp] theorem conc_app {n : Nat} (b a : Tm (n + 1)) (u : Tm0) :
    (b ∙ a)[u] = (b[u]) ∙ (a[u]) := rfl

@[simp] theorem conc_zero {n : Nat} (u : Tm0) : (𝐳𝐞𝐫𝐨 : Tm (n + 1))[u] = 𝐳𝐞𝐫𝐨 := rfl

@[simp] theorem conc_succ {n : Nat} (a : Tm (n + 1)) (u : Tm0) :
    (𝐬𝐮𝐜𝐜 a)[u] = 𝐬𝐮𝐜𝐜 (a[u]) := rfl

@[simp] theorem conc_nrec {n : Nat} (c₀ cs a : Tm (n + 1)) (u : Tm0) :
    (𝐧𝐫𝐞𝐜 c₀ cs a)[u] = 𝐧𝐫𝐞𝐜 (c₀[u]) (cs[u]) (a[u]) := rfl

@[simp] theorem abs_app {n : Nat} (x : Atom) (b a : Tm n) :
    (x ． b ∙ a) = (x ． b) ∙ (x ． a) := rfl

@[simp] theorem abs_zero {n : Nat} (x : Atom) : (x ． (𝐳𝐞𝐫𝐨 : Tm n)) = 𝐳𝐞𝐫𝐨 := rfl

@[simp] theorem abs_succ {n : Nat} (x : Atom) (a : Tm n) :
    (x ． 𝐬𝐮𝐜𝐜 a) = 𝐬𝐮𝐜𝐜 (x ． a) := rfl

@[simp] theorem abs_nrec {n : Nat} (x : Atom) (c₀ cs a : Tm n) :
    (x ． 𝐧𝐫𝐞𝐜 c₀ cs a) = 𝐧𝐫𝐞𝐜 (x ． c₀) (x ． cs) (x ． a) := rfl

/-! ## Decidability results about type expressions -/

/-- Agda: `𝐍𝐚𝐭?` (GST/Syntax.agda). -/
def natDec (A : Ty) : Dec (A = 𝐍𝐚𝐭) := Dec.ofDecidable (inferInstance)

/-- Agda: `⇒?` (GST/Syntax.agda). -/
def arrowDec (A B : Ty) : Dec { C : Ty // A = B ⇒ C } :=
  match A with
  | 𝐍𝐚𝐭 => .no fun p => by cases p.property
  | A₀ ⇒ A₁ =>
      if h : A₀ = B then .yes ⟨A₁, by rw [h]⟩
      else .no fun p => h (arrow_inj p.property).1

/-- Agda: `?⇒?` (GST/Syntax.agda). -/
def arrowDec₂ (A : Ty) : Dec (Σ B : Ty, { C : Ty // A = B ⇒ C }) :=
  match A with
  | 𝐍𝐚𝐭 => .no fun p => by cases p.2.property
  | A₀ ⇒ A₁ => .yes ⟨A₀, A₁, rfl⟩

end GST

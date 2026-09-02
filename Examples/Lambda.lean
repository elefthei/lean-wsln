import WSLN

/-!
# Untyped λ-calculus

Port of `agda-code/agda/Lambda.agda`: a well-scoped locally nameless
representation of the untyped λ-calculus, used as the running example of the
WSLN paper.

WSLN provides a `Nat`-indexed family `Trm sig n` with constructors `Trm.var` for
scoped de Bruijn indices (`Fin n`), `Trm.atom` for atomic names, and `Trm.op` for
compound terms.  λ-terms modulo α-equivalence are in bijection with the locally
closed (`n = 0`) terms.
-/

namespace Lambda

open WSLN

/-! ## The signature -/

inductive Op where
  /-- Function abstraction. -/
  | lm : Op
  /-- Function application. -/
  | ap : Op
  deriving DecidableEq

/-- Function abstraction takes one argument binding one name; function application
takes two arguments, each binding no names. -/
def ar : Op → List Nat
  | .lm => [1]
  | .ap => [0, 0]

def sig : Sig := ⟨Op, ar⟩

/-- Terms of the λ-calculus in scope `n`. -/
abbrev Tm (n : Nat) := WSLN.Trm sig n

instance : DecidableEq sig.Op := inferInstanceAs (DecidableEq Op)

/-! ## Concrete syntax -/

/-- Variable named by the atom `x`. -/
@[match_pattern] def vr {n : Nat} (x : Atom) : Tm n := .atom x

/-- Function abstraction. -/
@[match_pattern] def lam {n : Nat} (t : Tm (n + 1)) : Tm n := .op .lm (.cons t .nil)

/-- Function application. -/
@[match_pattern] def app {n : Nat} (b a : Tm n) : Tm n :=
  .op .ap (.cons b (.cons a .nil))

@[inherit_doc app] scoped infixl:70 " ∙ " => Lambda.app
@[inherit_doc lam] scoped notation:max "𝛌 " t:max => Lambda.lam t
@[inherit_doc vr] scoped notation:max "𝐯" x:max => Lambda.vr x

/-! ## Example term

The term corresponding to `λ x . λ y . x (y z)`, written first with raw
constructors and then with the concrete syntax. -/

section
variable (z : Atom)

def ex : Tm 0 :=
  .op .lm (.cons
    (.op .lm (.cons
      (.op .ap (.cons
        (.var ⟨1, by omega⟩)
        (.cons
          (.op .ap (.cons (.var ⟨0, by omega⟩) (.cons (.atom z) .nil)))
          .nil)))
      .nil))
    .nil)

/-- The same term using the concrete syntax. -/
def ex' : Tm 0 := 𝛌 (𝛌 (i1 ∙ (i0 ∙ 𝐯z)))

theorem ex_eq_ex' : ex z = ex' z := rfl

end

/-! ## One-step β-reduction -/

/-- One-step β-reduction. -/
inductive Step : Tm 0 → Tm 0 → Prop where
  /-- `t [ u ]` is the concretion of the 1-term `t` at the 0-term `u`. -/
  | beta (t : Tm 1) (u : Tm 0) : Step (Lambda.lam t ∙ u) (t[u])
  /-- `S : Fset` is a finite set of atoms; the premise is cofinitely quantified. -/
  | lam {t t' : Tm 1} (S : Fset) (h : ∀ x, x # S → Step (t[x]) (t'[x])) :
      Step (Lambda.lam t) (Lambda.lam t')
  | app₁ {u u' : Tm 0} (t : Tm 0) (h : Step u u') : Step (t ∙ u) (t ∙ u')
  | app₂ {t t' : Tm 0} (u : Tm 0) (h : Step t t') : Step (t ∙ u) (t' ∙ u)

@[inherit_doc Step] scoped infix:40 " ⟶β " => Lambda.Step

/-! ## Checks

These `example`s gate the build: they exercise that concretion, abstraction and
decidable equality all compute on concrete terms. -/

-- `beta` at a concrete redex: checks that `i0 [ 𝐚 3 ] = 𝐚 3` holds definitionally.
example : (𝛌 i0 ∙ (𝐯3 : Tm 0)) ⟶β (𝐯3 : Tm 0) := .beta i0 (𝐯3)

-- An instance of the cofinite `lam` rule: `λ y. (λ w. w) y ⟶β λ y. y`.
example : (𝛌 (𝛌 i0 ∙ i0) : Tm 0) ⟶β (𝛌 i0 : Tm 0) :=
  .lam ∅ fun x _ => .beta i0 (𝐯x)

-- `concAbs` on concrete terms.
example : ((5 : Atom) ． (𝐯5 : Tm 0))[(7 : Atom)] = (𝐯7 : Tm 0) := by
  rw [conc_atom, ← conc_trm, concAbs]
  exact updateEq Sb.id (Trm.atom 7) 5

-- The same equation by kernel computation, exercising `DecidableEq (Trm sig 0)`.
example : ((5 : Atom) ． (𝐯5 : Tm 0))[(7 : Atom)] = (𝐯7 : Tm 0) := by decide

-- `absConc`: abstracting a fresh concretion is the identity.
example : ((5 : Atom) ． (i0 : Tm 1)[(5 : Atom)]) = (i0 : Tm 1) :=
  absConc 5 i0 .empty

end Lambda

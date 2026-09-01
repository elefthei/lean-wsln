import MLTT.ExistsFresh

/-!
# Types of terms are unique up to conversion, and have a unique level

Port of `agda-code/agda/MLTT/Uniqueness.agda`.

Agda's `svTy` recurses on *two* derivations at once, peeling `⊢conv` on either side.
Lean's `Deriv.rec` takes a single scrutinee, so the right-hand `⊢conv` spine is peeled
once and for all by the auxiliary induction `toRoot`, which turns any derivation into
one whose last rule is not `⊢conv` (`Root`, the twelve non-conversion typing rules)
plus a conversion of the resulting type.  The main induction is then the outer one on
the first derivation, with the motive quantified over the second derivation, and a
`cases` on the `Root` evidence inside each case — the structure Agda's nested `with`
clauses describe.
-/

namespace MLTT

open WSLN
open Fset

/-! ## Variables have a unique type and level -/

/-- Agda: `svVr` (MLTT/Uniqueness.agda). -/
theorem svVr {l l' : Lvl} {Γ : Cx} {A A' : Ty0} {x x' : Atom} (p : Ok Γ)
    (q : (x, A, l) isIn Γ) (q' : (x', A', l') isIn Γ) (e : x = x') :
    (l = l') ∧ (A = A') := by
  revert p q q' e
  induction Γ with
  | nil => intro _ q _ _; cases q
  | snoc Γ₀ y B lB ih =>
      intro p q q' e
      cases q with
      | new =>
          cases q' with
          | new => exact ⟨rfl, rfl⟩
          | old q'' =>
              cases p with
              | snoc _ hfr _ =>
                  subst e
                  exact absurd (isIn_dom q'') (Fset.not_mem_of_notMem hfr)
      | old q'' =>
          cases q' with
          | new =>
              cases p with
              | snoc _ hfr _ =>
                  subst e
                  exact absurd (isIn_dom q'') (Fset.not_mem_of_notMem hfr)
          | old q''' =>
              cases p with
              | snoc _ _ hh => exact ih hh q'' q''' e

/-! ## Peeling the conversion rule

`Root Γ J` holds when `J` is derivable by a rule other than `⊢conv`.  It is a verbatim
copy of the twelve typing constructors of `Deriv` (`MLTT/Cofinite.lean`), with the same
premises, so that `rootDeriv` and `toRoot` are one-liners and `cases` on a `Root`
hypothesis whose subject term is known discriminates the twelve rules automatically. -/

/-- The twelve non-conversion typing rules of `Deriv`; no Agda counterpart. -/
private inductive Root : Cx → Jg → Prop where
  | var {Γ : Cx} {l : Lvl} {A : Ty0} {x : Atom}
      (q₀ : Ok Γ) (q₁ : (x, A, l) isIn Γ) : Root Γ (𝐯x ∶ A ⦂ l)
  | univ {Γ : Cx} {l : Lvl} (q : Ok Γ) : Root Γ (𝐔 l ⦂ (l + 1))
  | pi {Γ : Cx} {l l' : Lvl} {A : Ty0} {B : Ty 1} (S : Fset)
      (q₀ : Γ ⊢ A ⦂ l)
      (q₁ : ∀ x, x # S → (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l') :
      Root Γ (𝚷 l l' A B ⦂ max l l')
  | lam {Γ : Cx} {l l' : Lvl} {A : Ty0} {B : Ty 1} {b : Tm 1} (S : Fset)
      (q₀ : ∀ x, x # S → (Γ ⨟ x ∶ A ⦂ l) ⊢ b[x] ∶ B[x] ⦂ l')
      (h₀ : Γ ⊢ A ⦂ l)
      (h₁ : ∀ x, x # S → (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l') :
      Root Γ (𝛌 A b ∶ 𝚷 l l' A B ⦂ max l l')
  | app {Γ : Cx} {l l' : Lvl} {A : Ty0} {B : Ty 1} {a b : Tm0} (S : Fset)
      (q₀ : Γ ⊢ b ∶ 𝚷 l l' A B ⦂ max l l')
      (q₁ : Γ ⊢ a ∶ A ⦂ l)
      (q₂ : ∀ x, x # S → (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l')
      (h : Γ ⊢ A ⦂ l) :
      Root Γ (b ∙[ A, B ] a ∶ B[a] ⦂ l')
  | idF {Γ : Cx} {l : Lvl} {A a b : Tm0}
      (q₀ : Γ ⊢ a ∶ A ⦂ l) (q₁ : Γ ⊢ b ∶ A ⦂ l) (h : Γ ⊢ A ⦂ l) :
      Root Γ (𝐈𝐝 A a b ⦂ l)
  | reflI {Γ : Cx} {l : Lvl} {A : Ty0} {a : Tm0}
      (q : Γ ⊢ a ∶ A ⦂ l) (h : Γ ⊢ A ⦂ l) : Root Γ (𝐫𝐞𝐟𝐥 a ∶ 𝐈𝐝 A a a ⦂ l)
  | j {Γ : Cx} {l l' : Lvl} {A : Ty0} {C : Ty 2} {a b c e : Tm0} (S : Fset)
      (q₀ : ∀ x y, x # y # S →
        (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ 𝐈𝐝 A a (𝐯x) ⦂ l) ⊢ C[x][y] ⦂ l')
      (q₁ : Γ ⊢ a ∶ A ⦂ l)
      (q₂ : Γ ⊢ b ∶ A ⦂ l)
      (q₃ : Γ ⊢ c ∶ C[a][(𝐫𝐞𝐟𝐥 a : Tm0)] ⦂ l')
      (q₄ : Γ ⊢ e ∶ 𝐈𝐝 A a b ⦂ l)
      (h₀ : Γ ⊢ A ⦂ l)
      (h₁ : ∀ x, x # S → (Γ ⨟ x ∶ A ⦂ l) ⊢ 𝐈𝐝 A a (𝐯x) ⦂ l) :
      Root Γ (𝐉 C a b c e ∶ C[b][e] ⦂ l')
  | nat {Γ : Cx} (q : Ok Γ) : Root Γ (𝐍𝐚𝐭 ⦂ 0)
  | zero {Γ : Cx} (q : Ok Γ) : Root Γ (𝐳𝐞𝐫𝐨 ∶ 𝐍𝐚𝐭 ⦂ 0)
  | succ {Γ : Cx} {a : Tm0} (q : Γ ⊢ a ∶ 𝐍𝐚𝐭 ⦂ 0) : Root Γ (𝐬𝐮𝐜𝐜 a ∶ 𝐍𝐚𝐭 ⦂ 0)
  | nrec {Γ : Cx} {l : Lvl} {C : Ty 1} {c₀ a : Tm0} {cs : Tm 2} (S : Fset)
      (q₀ : Γ ⊢ c₀ ∶ C[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l)
      (q₁ : ∀ x y, x # y # S →
        (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C[x] ⦂ l) ⊢ cs[x][y] ∶ C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] ⦂ l)
      (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ⦂ 0)
      (h : ∀ x, x # S → (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C[x] ⦂ l) :
      Root Γ (𝐧𝐫𝐞𝐜 C c₀ cs a ∶ C[a] ⦂ l)

/-- `Root` is a sub-relation of `Deriv`. -/
private theorem rootDeriv {Γ : Cx} {J : Jg} (r : Root Γ J) : Γ ⊢ J := by
  cases r with
  | var q₀ q₁ => exact .var q₀ q₁
  | univ q => exact .univ q
  | pi S q₀ q₁ => exact .pi S q₀ q₁
  | lam S q₀ h₀ h₁ => exact .lam S q₀ h₀ h₁
  | app S q₀ q₁ q₂ h => exact .app S q₀ q₁ q₂ h
  | idF q₀ q₁ h => exact .idF q₀ q₁ h
  | reflI q h => exact .reflI q h
  | j S q₀ q₁ q₂ q₃ q₄ h₀ h₁ => exact .j S q₀ q₁ q₂ q₃ q₄ h₀ h₁
  | nat q => exact .nat q
  | zero q => exact .zero q
  | succ q => exact .succ q
  | nrec S q₀ q₁ q₂ h => exact .nrec S q₀ q₁ q₂ h

/-- The statement proved by induction for `toRoot`. -/
private def rootGoal (Γ : Cx) : Jg → Prop
  | .ty a A l => ∃ A₀ : Ty0, Root Γ (a ∶ A₀ ⦂ l) ∧ (Γ ⊢ A₀ ＝ A ⦂ l)
  | .eq _ _ _ _ => True

private theorem rootIntro {Γ : Cx} {a A : Tm0} {l : Lvl} (r : Root Γ (a ∶ A ⦂ l)) :
    rootGoal Γ (a ∶ A ⦂ l) := ⟨A, r, .refl (derivTyOfTm (rootDeriv r))⟩

set_option maxHeartbeats 1000000 in
/-- Every typing derivation is a non-conversion rule followed by a conversion of the
type.  This is the right-hand `⊢conv` peeling of Agda's `svTy`. -/
private theorem toRoot {Γ : Cx} {J : Jg} (d : Γ ⊢ J) : rootGoal Γ J := by
  induction d using Deriv.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc => trivial
  | conv _ q₁ ih₀ _ =>
      obtain ⟨A₀, hr, ee⟩ := ih₀
      exact ⟨A₀, hr, .trans ee q₁⟩
  | var q₀ q₁ => exact rootIntro (.var q₀ q₁)
  | univ q => exact rootIntro (.univ q)
  | pi S q₀ q₁ => exact rootIntro (.pi S q₀ q₁)
  | lam S q₀ h₀ h₁ => exact rootIntro (.lam S q₀ h₀ h₁)
  | app S q₀ q₁ q₂ h => exact rootIntro (.app S q₀ q₁ q₂ h)
  | idF q₀ q₁ h => exact rootIntro (.idF q₀ q₁ h)
  | reflI q h => exact rootIntro (.reflI q h)
  | j S q₀ q₁ q₂ q₃ q₄ h₀ h₁ => exact rootIntro (.j S q₀ q₁ q₂ q₃ q₄ h₀ h₁)
  | nat q => exact rootIntro (.nat q)
  | zero q => exact rootIntro (.zero q)
  | succ q => exact rootIntro (.succ q)
  | nrec S q₀ q₁ q₂ h => exact rootIntro (.nrec S q₀ q₁ q₂ h)
  | refl => trivial
  | symm => trivial
  | trans => trivial
  | eqConv => trivial
  | piCong => trivial
  | lamCong => trivial
  | appCong => trivial
  | idCong => trivial
  | reflCong => trivial
  | jCong => trivial
  | succCong => trivial
  | nrecCong => trivial
  | piBeta => trivial
  | idBeta => trivial
  | natBeta₀ => trivial
  | natBetaS => trivial
  | piEta => trivial

/-! ## Types of terms are unique up to conversion -/

/-- The statement proved by induction for `svTy`: Agda's `svTy` only has clauses for
the typing constructors, because its statement forces both judgements to be of the
form `a ∶ A ⦂ l`; Lean's `Deriv.rec` demands all thirty cases. -/
private def svTyGoal (Γ : Cx) : Jg → Prop
  | .ty a A l =>
      ∀ (A' : Ty0) (l' : Lvl), (Γ ⊢ a ∶ A' ⦂ l') → (l = l') ∧ (Γ ⊢ A ＝ A' ⦂ l)
  | .eq _ _ _ _ => True

set_option maxHeartbeats 1000000 in
/-- The induction behind `svTy`; see `svTyGoal`. -/
private theorem svTyAux {Γ : Cx} {J : Jg} (d : Γ ⊢ J) : svTyGoal Γ J := by
  induction d using Deriv.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc => trivial
  | conv _ q₁ ih₀ _ =>
      intro A'' l'' d'
      obtain ⟨el, r⟩ := ih₀ A'' l'' d'
      exact ⟨el, .trans (.symm q₁) r⟩
  | @var Γ l A x q₀ q₁ =>
      intro A' l' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | var q₀' q₁' =>
          obtain ⟨rfl, rfl⟩ := svVr q₀ q₁ q₁' rfl
          exact ⟨rfl, ee⟩
  | univ q =>
      intro A' l' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | univ _ => exact ⟨rfl, ee⟩
  | pi S q₀ q₁ =>
      intro A' l' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | pi _ _ _ => exact ⟨rfl, ee⟩
  | @lam Γ l l' A B b S q₀ h₀ h₁ ih₀ ih₁ _ =>
      intro A'' l'' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | @lam l₂ l₂' _ B₂ _ S' q₀' h₀' h₁' =>
          obtain ⟨eA, _⟩ := ih₁ _ _ h₀'
          have hl := Nat.succ.inj eA
          subst hl
          obtain ⟨x, hx⟩ := fresh (S, S', B, B₂)
          have hxS : x # S := notMem_union_left hx
          have hxS' : x # S' := notMem_union_left (notMem_union_right hx)
          have hxB : x # B :=
            notMem_union_left (notMem_union_right (notMem_union_right hx))
          have hxB₂ : x # B₂ :=
            notMem_union_right (notMem_union_right (notMem_union_right hx))
          obtain ⟨rfl, r⟩ := ih₀ x hxS _ _ (q₀' x hxS')
          exact ⟨rfl,
            .trans (piCongEF (.refl h₀) r (NotMem.union hxB hxB₂)) ee⟩
  | @app Γ l l' A B a b S q₀ q₁ q₂ h _ ih₁ ih₂ _ =>
      intro A'' l'' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | @app _ _ _ _ _ _ S' _ q₁' q₂' _ =>
          obtain ⟨rfl, _⟩ := ih₁ _ _ q₁'
          obtain ⟨x, hx⟩ := fresh (S, S')
          have hxS : x # S := notMem_union_left hx
          have hxS' : x # S' := notMem_union_right hx
          obtain ⟨eB, _⟩ := ih₂ x hxS _ _ (q₂' x hxS')
          have hl := Nat.succ.inj eB
          subst hl
          exact ⟨rfl, ee⟩
  | @idF Γ l A a b q₀ q₁ h ih₀ _ _ =>
      intro A'' l'' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | @idF _ _ _ _ q₀' _ _ =>
          obtain ⟨rfl, _⟩ := ih₀ _ _ q₀'
          exact ⟨rfl, ee⟩
  | @reflI Γ l A a q h ih₀ _ =>
      intro A'' l'' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | @reflI _ A₂ _ q' _ =>
          obtain ⟨rfl, r⟩ := ih₀ _ _ q'
          exact ⟨rfl, .trans (.idCong r (.refl q) (.refl q)) ee⟩
  | @j Γ l l' A C a b c ee₀ S q₀ q₁ q₂ q₃ q₄ h₀ h₁ _ _ _ ih₃ _ _ _ =>
      intro A'' l'' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | @j _ _ _ _ _ _ _ _ _ _ _ _ q₃' _ _ _ =>
          obtain ⟨rfl, _⟩ := ih₃ _ _ q₃'
          exact ⟨rfl, ee⟩
  | nat q =>
      intro A' l' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | nat _ => exact ⟨rfl, ee⟩
  | zero q =>
      intro A' l' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | zero _ => exact ⟨rfl, ee⟩
  | succ q =>
      intro A' l' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | succ _ => exact ⟨rfl, ee⟩
  | @nrec Γ l C c₀ a cs S q₀ q₁ q₂ h ih₀ _ _ _ =>
      intro A'' l'' d'
      obtain ⟨A₀, hr, ee⟩ := toRoot d'
      cases hr with
      | @nrec _ _ _ _ _ _ q₀' _ _ _ =>
          obtain ⟨rfl, _⟩ := ih₀ _ _ q₀'
          exact ⟨rfl, ee⟩
  | refl => trivial
  | symm => trivial
  | trans => trivial
  | eqConv => trivial
  | piCong => trivial
  | lamCong => trivial
  | appCong => trivial
  | idCong => trivial
  | reflCong => trivial
  | jCong => trivial
  | succCong => trivial
  | nrecCong => trivial
  | piBeta => trivial
  | idBeta => trivial
  | natBeta₀ => trivial
  | natBetaS => trivial
  | piEta => trivial

/-- Agda: `svTy` (MLTT/Uniqueness.agda). -/
theorem svTy {l l' : Lvl} {Γ : Cx} {A A' : Ty0} {a : Tm0} (q : Γ ⊢ a ∶ A ⦂ l)
    (q' : Γ ⊢ a ∶ A' ⦂ l') : (l = l') ∧ (Γ ⊢ A ＝ A' ⦂ l) := svTyAux q A' l' q'

/-! ## Checks

These `example`s and `#print axioms` commands gate the build: they exercise that the
cofinite rules, the exists-fresh rules and uniqueness of types are usable on concrete
derivations, and that nothing in the development depends on `sorryAx`. -/

section Checks

/-- `Ok` of the one-entry context `◇ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0`. -/
private theorem okNat (x : Atom) : Ok (◇ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) :=
  .snoc (.nat .nil) .empty .nil

-- ℕ is a type in the empty context.
example : ◇ ⊢ (𝐍𝐚𝐭 : Ty0) ⦂ 0 := .nat .nil

-- `zero : ℕ`.
example : ◇ ⊢ (𝐳𝐞𝐫𝐨 : Tm0) ∶ 𝐍𝐚𝐭 ⦂ 0 := .zero .nil

-- The identity function on ℕ, via the cofinite λ-rule.
example : ◇ ⊢ 𝛌 (𝐍𝐚𝐭 : Ty0) (i0 : Tm 1) ∶ 𝚷 0 0 (𝐍𝐚𝐭 : Ty0) (𝐍𝐚𝐭 : Ty 1) ⦂ max 0 0 :=
  .lam ∅ (fun x _ => .var (okNat x) .new) (.nat .nil) (fun x _ => .nat (okNat x))

-- The same, via the *exists-fresh* λ-rule at the single atom `x := 0`, discharging
-- the freshness side condition `0 # (𝐍𝐚𝐭, i0)` by kernel computation.
example : ◇ ⊢ 𝛌 (𝐍𝐚𝐭 : Ty0) (i0 : Tm 1) ∶ 𝚷 0 0 (𝐍𝐚𝐭 : Ty0) (𝐍𝐚𝐭 : Ty 1) ⦂ max 0 0 :=
  lamEF (x := 0) (.var (okNat 0) .new) (by decide)

-- The dependent function type `Π x : ℕ. ℕ`, via the exists-fresh Π-rule.
example : ◇ ⊢ 𝚷 0 0 (𝐍𝐚𝐭 : Ty0) (𝐍𝐚𝐭 : Ty 1) ⦂ max 0 0 :=
  piEF (x := 0) (.nat .nil) (.nat (okNat 0)) (by decide)

-- Uniqueness of types on a concrete pair of derivations.
example : (0 : Lvl) = 0 ∧ (◇ ⊢ (𝐍𝐚𝐭 : Ty0) ＝ 𝐍𝐚𝐭 ⦂ 0) :=
  svTy (Deriv.zero .nil) (Deriv.zero .nil)

#print axioms derivSupp
#print axioms wkDeriv
#print axioms sbDeriv
#print axioms eqSbTm
#print axioms derivTy₁
#print axioms piEtaEF
#print axioms svTy

end Checks

end MLTT


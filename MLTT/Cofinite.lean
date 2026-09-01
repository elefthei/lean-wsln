import MLTT.Judgement

/-!
# Provable judgements, with cofinite quantification over fresh names

Port of `agda-code/agda/MLTT/Cofinite.agda`.

Some rules include helper hypotheses that aid proofs by structural induction;
versions of those rules without the helpers are admissible — see
`MLTT/ExistsFresh.lean` and `MLTT/Admissible.lean`.

Agda declares `Γ` as a *parameter* of `_⊢_`, even though the cofinite premises
mention extended contexts.  In Lean the context is an *index*, which is strictly
more permissive and needs no further justification.
-/

namespace MLTT

open WSLN

mutual

/-- Agda: `Ok` (MLTT/Cofinite.agda). Well-formed contexts. -/
inductive Ok : Cx → Prop where
  /-- Agda: `ok◇`. -/
  | nil : Ok ◇
  /-- Agda: `ok⨟`.  The final `Ok Γ` is a helper hypothesis. -/
  | snoc {l : Lvl} {Γ : Cx} {A : Ty0} {x : Atom}
      (q₀ : Deriv Γ (A ⦂ l)) (q₁ : x # Γ) (h : Ok Γ) : Ok (Γ ⨟ x ∶ A ⦂ l)

/-- Agda: `_⊢_` (MLTT/Cofinite.agda). -/
inductive Deriv : Cx → Jg → Prop where
  -- Well-formed terms: `Γ ⊢ a ∶ A ⦂ l`

  /-- Agda: `⊢conv`. -/
  | conv {Γ : Cx} {l : Lvl} {a : Tm0} {A A' : Ty0}
      (q₀ : Deriv Γ (a ∶ A ⦂ l)) (q₁ : Deriv Γ (A ＝ A' ⦂ l)) :
      Deriv Γ (a ∶ A' ⦂ l)

  /-- Agda: `⊢𝐯`. -/
  | var {Γ : Cx} {l : Lvl} {A : Ty0} {x : Atom}
      (q₀ : Ok Γ) (q₁ : (x, A, l) isIn Γ) : Deriv Γ (𝐯x ∶ A ⦂ l)

  /-- Agda: `⊢𝐔`. -/
  | univ {Γ : Cx} {l : Lvl} (q : Ok Γ) : Deriv Γ (𝐔 l ⦂ (l + 1))

  /-- Agda: `⊢𝚷`. -/
  | pi {Γ : Cx} {l l' : Lvl} {A : Ty0} {B : Ty 1} (S : Fset)
      (q₀ : Deriv Γ (A ⦂ l))
      (q₁ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (B[x] ⦂ l')) :
      Deriv Γ (𝚷 l l' A B ⦂ max l l')

  /-- Agda: `⊢𝛌`.  The last two premises are helper hypotheses. -/
  | lam {Γ : Cx} {l l' : Lvl} {A : Ty0} {B : Ty 1} {b : Tm 1} (S : Fset)
      (q₀ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (b[x] ∶ B[x] ⦂ l'))
      (h₀ : Deriv Γ (A ⦂ l))
      (h₁ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (B[x] ⦂ l')) :
      Deriv Γ (𝛌 A b ∶ 𝚷 l l' A B ⦂ max l l')

  /-- Agda: `⊢∙`.  The last premise is a helper hypothesis. -/
  | app {Γ : Cx} {l l' : Lvl} {A : Ty0} {B : Ty 1} {a b : Tm0} (S : Fset)
      (q₀ : Deriv Γ (b ∶ 𝚷 l l' A B ⦂ max l l'))
      (q₁ : Deriv Γ (a ∶ A ⦂ l))
      (q₂ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (B[x] ⦂ l'))
      (h : Deriv Γ (A ⦂ l)) :
      Deriv Γ (b ∙[ A, B ] a ∶ B[a] ⦂ l')

  /-- Agda: `⊢𝐈𝐝`.  The last premise is a helper hypothesis. -/
  | idF {Γ : Cx} {l : Lvl} {A a b : Tm0}
      (q₀ : Deriv Γ (a ∶ A ⦂ l)) (q₁ : Deriv Γ (b ∶ A ⦂ l)) (h : Deriv Γ (A ⦂ l)) :
      Deriv Γ (𝐈𝐝 A a b ⦂ l)

  /-- Agda: `⊢𝐫𝐞𝐟𝐥`.  The last premise is a helper hypothesis. -/
  | reflI {Γ : Cx} {l : Lvl} {A : Ty0} {a : Tm0}
      (q : Deriv Γ (a ∶ A ⦂ l)) (h : Deriv Γ (A ⦂ l)) :
      Deriv Γ (𝐫𝐞𝐟𝐥 a ∶ 𝐈𝐝 A a a ⦂ l)

  /-- Agda: `⊢𝐉`.  The last two premises are helper hypotheses. -/
  | j {Γ : Cx} {l l' : Lvl} {A : Ty0} {C : Ty 2} {a b c e : Tm0} (S : Fset)
      (q₀ : ∀ x y, x # y # S →
        Deriv (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ 𝐈𝐝 A a (𝐯x) ⦂ l) (C[x][y] ⦂ l'))
      (q₁ : Deriv Γ (a ∶ A ⦂ l))
      (q₂ : Deriv Γ (b ∶ A ⦂ l))
      (q₃ : Deriv Γ (c ∶ C[a][𝐫𝐞𝐟𝐥 a] ⦂ l'))
      (q₄ : Deriv Γ (e ∶ 𝐈𝐝 A a b ⦂ l))
      (h₀ : Deriv Γ (A ⦂ l))
      (h₁ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (𝐈𝐝 A a (𝐯x) ⦂ l)) :
      Deriv Γ (𝐉 C a b c e ∶ C[b][e] ⦂ l')

  /-- Agda: `⊢𝐍𝐚𝐭`. -/
  | nat {Γ : Cx} (q : Ok Γ) : Deriv Γ (𝐍𝐚𝐭 ⦂ 0)

  /-- Agda: `⊢𝐳𝐞𝐫𝐨`. -/
  | zero {Γ : Cx} (q : Ok Γ) : Deriv Γ (𝐳𝐞𝐫𝐨 ∶ 𝐍𝐚𝐭 ⦂ 0)

  /-- Agda: `⊢𝐬𝐮𝐜𝐜`. -/
  | succ {Γ : Cx} {a : Tm0} (q : Deriv Γ (a ∶ 𝐍𝐚𝐭 ⦂ 0)) :
      Deriv Γ (𝐬𝐮𝐜𝐜 a ∶ 𝐍𝐚𝐭 ⦂ 0)

  /-- Agda: `⊢𝐧𝐫𝐞𝐜`.  The last premise is a helper hypothesis. -/
  | nrec {Γ : Cx} {l : Lvl} {C : Ty 1} {c₀ a : Tm0} {cs : Tm 2} (S : Fset)
      (q₀ : Deriv Γ (c₀ ∶ C[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l))
      (q₁ : ∀ x y, x # y # S →
        Deriv (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C[x] ⦂ l) (cs[x][y] ∶ C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] ⦂ l))
      (q₂ : Deriv Γ (a ∶ 𝐍𝐚𝐭 ⦂ 0))
      (h : ∀ x, x # S → Deriv (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) (C[x] ⦂ l)) :
      Deriv Γ (𝐧𝐫𝐞𝐜 C c₀ cs a ∶ C[a] ⦂ l)

  -- Term conversion: `Γ ⊢ a ＝ a' ∶ A ⦂ l`

  /-- Agda: `Refl`. -/
  | refl {Γ : Cx} {l : Lvl} {A : Ty0} {a : Tm0} (q : Deriv Γ (a ∶ A ⦂ l)) :
      Deriv Γ (a ＝ a ∶ A ⦂ l)

  /-- Agda: `Symm`. -/
  | symm {Γ : Cx} {l : Lvl} {A : Ty0} {a a' : Tm0} (q : Deriv Γ (a ＝ a' ∶ A ⦂ l)) :
      Deriv Γ (a' ＝ a ∶ A ⦂ l)

  /-- Agda: `Trans`. -/
  | trans {Γ : Cx} {l : Lvl} {A : Ty0} {a a' a'' : Tm0}
      (q₀ : Deriv Γ (a ＝ a' ∶ A ⦂ l)) (q₁ : Deriv Γ (a' ＝ a'' ∶ A ⦂ l)) :
      Deriv Γ (a ＝ a'' ∶ A ⦂ l)

  /-- Agda: `＝conv`. -/
  | eqConv {Γ : Cx} {l : Lvl} {A A' : Ty0} {a a' : Tm0}
      (q₀ : Deriv Γ (a ＝ a' ∶ A ⦂ l)) (q₁ : Deriv Γ (A ＝ A' ⦂ l)) :
      Deriv Γ (a ＝ a' ∶ A' ⦂ l)

  /-- Agda: `𝚷Cong`.  The last premise is a helper hypothesis. -/
  | piCong {Γ : Cx} {l l' : Lvl} {A A' : Ty0} {B B' : Ty 1} (S : Fset)
      (q₀ : Deriv Γ (A ＝ A' ⦂ l))
      (q₁ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (B[x] ＝ B'[x] ⦂ l'))
      (h : Deriv Γ (A ⦂ l)) :
      Deriv Γ (𝚷 l l' A B ＝ 𝚷 l l' A' B' ⦂ max l l')

  /-- Agda: `𝛌Cong`.  The last two premises are helper hypotheses. -/
  | lamCong {Γ : Cx} {l l' : Lvl} {A A' : Ty0} {B : Ty 1} {b b' : Tm 1} (S : Fset)
      (q₀ : Deriv Γ (A ＝ A' ⦂ l))
      (q₁ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (b[x] ＝ b'[x] ∶ B[x] ⦂ l'))
      (h₀ : Deriv Γ (A ⦂ l))
      (h₁ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (B[x] ⦂ l')) :
      Deriv Γ (𝛌 A b ＝ 𝛌 A' b' ∶ 𝚷 l l' A B ⦂ max l l')

  /-- Agda: `∙Cong`.  The last two premises are helper hypotheses. -/
  | appCong {Γ : Cx} {l l' : Lvl} {A A' : Ty0} {B B' : Ty 1} {a a' b b' : Tm0}
      (S : Fset)
      (q₀ : Deriv Γ (A ＝ A' ⦂ l))
      (q₁ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (B[x] ＝ B'[x] ⦂ l'))
      (q₂ : Deriv Γ (b ＝ b' ∶ 𝚷 l l' A B ⦂ max l l'))
      (q₃ : Deriv Γ (a ＝ a' ∶ A ⦂ l))
      (h₀ : Deriv Γ (A ⦂ l))
      (h₁ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (B[x] ⦂ l')) :
      Deriv Γ (b ∙[ A, B ] a ＝ b' ∙[ A', B' ] a' ∶ B[a] ⦂ l')

  /-- Agda: `𝐈𝐝Cong`. -/
  | idCong {Γ : Cx} {l : Lvl} {A A' : Ty0} {a a' b b' : Tm0}
      (q₀ : Deriv Γ (A ＝ A' ⦂ l))
      (q₁ : Deriv Γ (a ＝ a' ∶ A ⦂ l))
      (q₂ : Deriv Γ (b ＝ b' ∶ A ⦂ l)) :
      Deriv Γ (𝐈𝐝 A a b ＝ 𝐈𝐝 A' a' b' ⦂ l)

  /-- Agda: `𝐫𝐞𝐟𝐥Cong`.  The last premise is a helper hypothesis. -/
  | reflCong {Γ : Cx} {l : Lvl} {A : Ty0} {a a' : Tm0}
      (q : Deriv Γ (a ＝ a' ∶ A ⦂ l)) (h : Deriv Γ (A ⦂ l)) :
      Deriv Γ (𝐫𝐞𝐟𝐥 a ＝ 𝐫𝐞𝐟𝐥 a' ∶ 𝐈𝐝 A a a ⦂ l)

  /-- Agda: `𝐉Cong`.  The last two premises are helper hypotheses. -/
  | jCong {Γ : Cx} {l l' : Lvl} {A : Ty0} {C C' : Ty 2}
      {a a' b b' c c' e e' : Tm0} (S : Fset)
      (q₀ : ∀ x y, x # y # S →
        Deriv (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ 𝐈𝐝 A a (𝐯x) ⦂ l) (C[x][y] ＝ C'[x][y] ⦂ l'))
      (q₁ : Deriv Γ (a ＝ a' ∶ A ⦂ l))
      (q₂ : Deriv Γ (b ＝ b' ∶ A ⦂ l))
      (q₃ : Deriv Γ (c ＝ c' ∶ C[a][𝐫𝐞𝐟𝐥 a] ⦂ l'))
      (q₄ : Deriv Γ (e ＝ e' ∶ 𝐈𝐝 A a b ⦂ l))
      (h₀ : Deriv Γ (A ⦂ l))
      (h₁ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (𝐈𝐝 A a (𝐯x) ⦂ l)) :
      Deriv Γ (𝐉 C a b c e ＝ 𝐉 C' a' b' c' e' ∶ C[b][e] ⦂ l')

  /-- Agda: `𝐬𝐮𝐜𝐜Cong`. -/
  | succCong {Γ : Cx} {a a' : Tm0} (q : Deriv Γ (a ＝ a' ∶ 𝐍𝐚𝐭 ⦂ 0)) :
      Deriv Γ (𝐬𝐮𝐜𝐜 a ＝ 𝐬𝐮𝐜𝐜 a' ∶ 𝐍𝐚𝐭 ⦂ 0)

  /-- Agda: `𝐧𝐫𝐞𝐜Cong`.  The last premise is a helper hypothesis. -/
  | nrecCong {Γ : Cx} {l : Lvl} {C C' : Ty 1} {c₀ c₀' a a' : Tm0} {cs cs' : Tm 2}
      (S : Fset)
      (q₀ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) (C[x] ＝ C'[x] ⦂ l))
      (q₁ : Deriv Γ (c₀ ＝ c₀' ∶ C[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l))
      (q₂ : ∀ x y, x # y # S →
        Deriv (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C[x] ⦂ l)
          (cs[x][y] ＝ cs'[x][y] ∶ C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] ⦂ l))
      (q₃ : Deriv Γ (a ＝ a' ∶ 𝐍𝐚𝐭 ⦂ 0))
      (h : ∀ x, x # S → Deriv (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) (C[x] ⦂ l)) :
      Deriv Γ (𝐧𝐫𝐞𝐜 C c₀ cs a ＝ 𝐧𝐫𝐞𝐜 C' c₀' cs' a' ∶ C[a] ⦂ l)

  /-- Agda: `𝚷Beta`.  The last two premises are helper hypotheses. -/
  | piBeta {Γ : Cx} {l l' : Lvl} {A : Ty0} {a : Tm0} {B : Ty 1} {b : Tm 1} (S : Fset)
      (q₀ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (b[x] ∶ B[x] ⦂ l'))
      (q₁ : Deriv Γ (a ∶ A ⦂ l))
      (h₀ : Deriv Γ (A ⦂ l))
      (h₁ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (B[x] ⦂ l')) :
      Deriv Γ (𝛌 A b ∙[ A, B ] a ＝ b[a] ∶ B[a] ⦂ l')

  /-- Agda: `𝐈𝐝Beta`.  The last two premises are helper hypotheses. -/
  | idBeta {Γ : Cx} {l l' : Lvl} {A : Ty0} {C : Ty 2} {a c : Tm0} (S : Fset)
      (q₀ : ∀ x y, x # y # S →
        Deriv (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ 𝐈𝐝 A a (𝐯x) ⦂ l) (C[x][y] ⦂ l'))
      (q₁ : Deriv Γ (a ∶ A ⦂ l))
      (q₂ : Deriv Γ (c ∶ C[a][𝐫𝐞𝐟𝐥 a] ⦂ l'))
      (h₀ : Deriv Γ (A ⦂ l))
      (h₁ : ∀ x, x # S → Deriv (Γ ⨟ x ∶ A ⦂ l) (𝐈𝐝 A a (𝐯x) ⦂ l)) :
      Deriv Γ (𝐉 C a a c (𝐫𝐞𝐟𝐥 a) ＝ c ∶ C[a][𝐫𝐞𝐟𝐥 a] ⦂ l')

  /-- Agda: `𝐍𝐚𝐭Beta₀`.  The last premise is a helper hypothesis. -/
  | natBeta₀ {Γ : Cx} {l : Lvl} {C : Ty 1} {c₀ : Tm0} {cs : Tm 2} (S : Fset)
      (q₀ : Deriv Γ (c₀ ∶ C[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l))
      (q₁ : ∀ x y, x # y # S →
        Deriv (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C[x] ⦂ l) (cs[x][y] ∶ C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] ⦂ l))
      (h : ∀ x, x # S → Deriv (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) (C[x] ⦂ l)) :
      Deriv Γ (𝐧𝐫𝐞𝐜 C c₀ cs 𝐳𝐞𝐫𝐨 ＝ c₀ ∶ C[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l)

  /-- Agda: `𝐍𝐚𝐭Beta₊`.  The last premise is a helper hypothesis. -/
  | natBetaS {Γ : Cx} {l : Lvl} {C : Ty 1} {c₀ a : Tm0} {cs : Tm 2} (S : Fset)
      (q₀ : Deriv Γ (c₀ ∶ C[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l))
      (q₁ : ∀ x y, x # y # S →
        Deriv (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C[x] ⦂ l) (cs[x][y] ∶ C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] ⦂ l))
      (q₂ : Deriv Γ (a ∶ 𝐍𝐚𝐭 ⦂ 0))
      (h : ∀ x, x # S → Deriv (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) (C[x] ⦂ l)) :
      Deriv Γ (𝐧𝐫𝐞𝐜 C c₀ cs (𝐬𝐮𝐜𝐜 a) ＝ cs[a][𝐧𝐫𝐞𝐜 C c₀ cs a] ∶ C[𝐬𝐮𝐜𝐜 a] ⦂ l)

  /-- Agda: `𝚷Eta`.  The last premise is a helper hypothesis. -/
  | piEta {Γ : Cx} {l l' : Lvl} {A : Ty0} {B : Ty 1} {b b' : Tm0} (S : Fset)
      (q₀ : Deriv Γ (b ∶ 𝚷 l l' A B ⦂ max l l'))
      (q₁ : Deriv Γ (b' ∶ 𝚷 l l' A B ⦂ max l l'))
      (q₂ : ∀ x, x # S →
        Deriv (Γ ⨟ x ∶ A ⦂ l) (b ∙[ A, B ] 𝐯x ＝ b' ∙[ A, B ] 𝐯x ∶ B[x] ⦂ l'))
      (h : Deriv Γ (A ⦂ l)) :
      Deriv Γ (b ＝ b' ∶ 𝚷 l l' A B ⦂ max l l')

end

@[inherit_doc Deriv] scoped notation:25 Γ:26 " ⊢ " J:26 => MLTT.Deriv Γ J

/-! ## Transport of judgements along equalities

Agda's `subst`/`subst₂`/`subst₃` specialised to the four judgement forms.  Lean-only
plumbing, shared by `MLTT/Substitution.lean`, `MLTT/Admissible.lean` and
`MLTT/ExistsFresh.lean`. -/

/-- Agda's `subst` on a `_⦂_` judgement. -/
theorem castIsTy {Γ : Cx} {l : Lvl} {A A' : Ty0} (e : A = A')
    (d : Γ ⊢ A ⦂ l) : Γ ⊢ A' ⦂ l :=
  WSLN.subst (fun A => Deriv Γ (Jg.isTy A l)) e d

/-- Agda's `subst₂` on a `_＝_⦂_` judgement. -/
theorem castTyEq {Γ : Cx} {l : Lvl} {A A' B B' : Ty0} (e : A = A')
    (e' : B = B') (d : Γ ⊢ A ＝ B ⦂ l) : Γ ⊢ A' ＝ B' ⦂ l :=
  WSLN.subst₂ (fun A B => Deriv Γ (Jg.tyEq A B l)) e e' d

/-- Agda's `subst₂` on a `_∶_⦂_` judgement. -/
theorem castTm {Γ : Cx} {l : Lvl} {a a' : Tm0} {A A' : Ty0} (e : a = a')
    (e' : A = A') (d : Γ ⊢ a ∶ A ⦂ l) : Γ ⊢ a' ∶ A' ⦂ l :=
  WSLN.subst₂ (fun a A => Deriv Γ (Jg.ty a A l)) e e' d

/-- Agda's `subst₃` on a `_＝_∶_⦂_` judgement. -/
theorem castEq {Γ : Cx} {l : Lvl} {a a' b b' : Tm0} {A A' : Ty0}
    (e : a = a') (e' : b = b') (e'' : A = A') (d : Γ ⊢ a ＝ b ∶ A ⦂ l) :
    Γ ⊢ a' ＝ b' ∶ A' ⦂ l :=
  WSLN.subst₃ (fun a b A => Deriv Γ (Jg.eq a b A l)) e e' e'' d

/-! ## Context conversion -/

/-- Agda: `⊢_＝_` (MLTT/Cofinite.agda). -/
inductive CxEq : Cx → Cx → Prop where
  /-- Agda: `＝◇`. -/
  | nil : CxEq ◇ ◇
  /-- Agda: `＝⨟`.  The last two premises are helper hypotheses. -/
  | snoc {l : Lvl} {Γ Γ' : Cx} {A A' : Ty0} {x : Atom}
      (q₀ : CxEq Γ Γ') (q₁ : Γ ⊢ A ＝ A' ⦂ l) (q₂ : x # (Γ, Γ'))
      (h₀ : Γ ⊢ A ⦂ l) (h₁ : Γ' ⊢ A' ⦂ l) :
      CxEq (Γ ⨟ x ∶ A ⦂ l) (Γ' ⨟ x ∶ A' ⦂ l)

@[inherit_doc CxEq] scoped notation:25 "⊢ " Γ:41 " ＝ " Γ':41 => MLTT.CxEq Γ Γ'

/-! ## Context weakening -/

/-- Agda: `_▷_` (MLTT/Cofinite.agda). -/
inductive Weakens : Cx → Cx → Prop where
  /-- Agda: `▷◇`. -/
  | nil : Weakens ◇ ◇
  /-- Agda: `▷proj`. -/
  | proj {l : Lvl} {Δ Γ : Cx} {A : Ty0} {x : Atom}
      (q₀ : Weakens Δ Γ) (q₁ : Δ ⊢ A ⦂ l) (q₂ : x # Δ) :
      Weakens (Δ ⨟ x ∶ A ⦂ l) Γ
  /-- Agda: `▷⨟`.  The final premise is a helper hypothesis. -/
  | snoc {l : Lvl} {Δ Γ : Cx} {A : Ty0} {x : Atom}
      (q₀ : Weakens Δ Γ) (q₁ : Γ ⊢ A ⦂ l) (q₂ : x # Δ) (h : Δ ⊢ A ⦂ l) :
      Weakens (Δ ⨟ x ∶ A ⦂ l) (Γ ⨟ x ∶ A ⦂ l)

@[inherit_doc Weakens] scoped notation:25 Δ:26 " ▷ " Γ:26 => MLTT.Weakens Δ Γ

/-! ## Well-typed substitutions -/

/-- Agda: `_⊢ˢ_∶_` (MLTT/Cofinite.agda). -/
inductive SbTyping : Cx → Sb sig → Cx → Prop where
  /-- Agda: `◇ˢ`. -/
  | nil {Γ' : Cx} {σ : Sb sig} (q : Ok Γ') : SbTyping Γ' σ ◇
  /-- Agda: `⨟ˢ`. -/
  | snoc {l : Lvl} {Γ Γ' : Cx} {σ : Sb sig} {A : Ty0} {x : Atom}
      (q₀ : SbTyping Γ' σ Γ) (q₁ : Γ ⊢ A ⦂ l) (q₂ : Γ' ⊢ σ x ∶ σ * A ⦂ l)
      (q₃ : x # Γ) :
      SbTyping Γ' σ (Γ ⨟ x ∶ A ⦂ l)

@[inherit_doc SbTyping]
scoped notation:25 Γ':26 " ⊢ˢ " σ:41 " ∶ " Γ:41 => MLTT.SbTyping Γ' σ Γ

/-! ## Well-typed renamings -/

/-- Agda: `_⊢ʳ_∶_` (MLTT/Cofinite.agda). -/
def RnTyping (Δ : Cx) (ρ : Rn) (Γ : Cx) : Prop := SbTyping Δ (Sb.ofRn ρ) Γ

@[inherit_doc RnTyping]
scoped notation:25 Δ:26 " ⊢ʳ " ρ:41 " ∶ " Γ:41 => MLTT.RnTyping Δ ρ Γ

/-! ## Convertible well-typed substitutions -/

/-- Agda: `_⊢ˢ_＝_∶_` (MLTT/Cofinite.agda). -/
inductive SbEqTyping : Cx → Sb sig → Sb sig → Cx → Prop where
  /-- Agda: `＝◇ˢ`. -/
  | nil {Γ' : Cx} {σ σ' : Sb sig} (q : Ok Γ') : SbEqTyping Γ' σ σ' ◇
  /-- Agda: `＝⨟ˢ`. -/
  | snoc {l : Lvl} {Γ Γ' : Cx} {σ σ' : Sb sig} {A : Ty0} {x : Atom}
      (q₀ : SbEqTyping Γ' σ σ' Γ) (q₁ : Γ ⊢ A ⦂ l)
      (q₂ : Γ' ⊢ σ x ＝ σ' x ∶ σ * A ⦂ l) (q₃ : x # Γ) :
      SbEqTyping Γ' σ σ' (Γ ⨟ x ∶ A ⦂ l)

@[inherit_doc SbEqTyping]
scoped notation:25 Γ':26 " ⊢ˢ " σ:41 " ＝ " σ':41 " ∶ " Γ:41 =>
  MLTT.SbEqTyping Γ' σ σ' Γ

end MLTT

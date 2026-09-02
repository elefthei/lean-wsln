import GST.Context

/-!
# Typing and βη-conversion

Port of `agda-code/agda/GST/TypeSystem.agda`.

Both judgements are *exists-fresh*: the binding rules quantify over one atom `x`
together with the two side conditions `x # Γ` (here the explicit `h : x ∉ᶠ S`) and
`x # b`.  `GST/Renaming.lean` proves the corresponding "for all fresh atoms" forms
(`rn⊢¹`, `rn＝¹`).

Agda takes the context as a parameter of the two judgements; here it is an index,
because the λ-rules mention the extended context `Γ ⨟ x ∶ A ∣ h`.

Both judgements are `Type`-valued, exactly as in Agda: `GST/TermSemantics.lean`
interprets a *derivation* as a natural transformation, and `⊢ty₁`/`⊢ty₂`
(`GST/Substitution.lean`) turn a conversion derivation into a typing derivation, so
neither can live in `Prop`.
-/

namespace GST

open WSLN

/-! ## Typing -/

/-- Agda: `_⊢_∶_` (GST/TypeSystem.agda). -/
inductive Deriv : {S : Fset} → Cx S → Tm0 → Ty → Type where
  /-- Agda: `Var`. -/
  | var {S : Fset} {Γ : Cx S} {A : Ty} {x : Atom} (q : (x, A) isIn Γ) :
      Deriv Γ (𝐯x) A
  /-- Agda: `Lam`. -/
  | lam {S : Fset} {Γ : Cx S} {A B : Ty} {b : Tm 1} {x : Atom} {h : x ∉ᶠ S}
      (q₀ : Deriv (Γ ⨟ x ∶ A ∣ h) (b[x]) B) (q₁ : x # b) : Deriv Γ (𝛌 A b) (A ⇒ B)
  /-- Agda: `App`. -/
  | app {S : Fset} {Γ : Cx S} {A B : Ty} {a b : Tm0} (q₀ : Deriv Γ b (A ⇒ B))
      (q₁ : Deriv Γ a A) : Deriv Γ (b ∙ a) B
  /-- Agda: `Zero`. -/
  | zero {S : Fset} {Γ : Cx S} : Deriv Γ 𝐳𝐞𝐫𝐨 𝐍𝐚𝐭
  /-- Agda: `Succ`. -/
  | succ {S : Fset} {Γ : Cx S} {a : Tm0} (q : Deriv Γ a 𝐍𝐚𝐭) : Deriv Γ (𝐬𝐮𝐜𝐜 a) 𝐍𝐚𝐭
  /-- Agda: `Nrec`. -/
  | nrec {S : Fset} {Γ : Cx S} {C : Ty} {c₀ cs a : Tm0} (q₀ : Deriv Γ c₀ C)
      (q₁ : Deriv Γ cs (𝐍𝐚𝐭 ⇒ C ⇒ C)) (q₂ : Deriv Γ a 𝐍𝐚𝐭) :
      Deriv Γ (𝐧𝐫𝐞𝐜 c₀ cs a) C

@[inherit_doc Deriv]
scoped notation:25 Γ:26 " ⊢ " a:26 " ∶ " A:26 => GST.Deriv Γ a A

/-! ## Conversion -/

/-- Agda: `_⊢_＝_∶_` (GST/TypeSystem.agda). -/
inductive Conv : {S : Fset} → Cx S → Tm0 → Tm0 → Ty → Type where
  /-- Agda: `Refl`. -/
  | refl {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} (q : Γ ⊢ a ∶ A) : Conv Γ a a A
  /-- Agda: `Symm`. -/
  | symm {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} (q : Conv Γ a a' A) :
      Conv Γ a' a A
  /-- Agda: `Trans`. -/
  | trans {S : Fset} {Γ : Cx S} {A : Ty} {a a' a'' : Tm0} (q₀ : Conv Γ a a' A)
      (q₁ : Conv Γ a' a'' A) : Conv Γ a a'' A
  /-- Agda: `Lam`. -/
  | lam {S : Fset} {Γ : Cx S} {A B : Ty} {b b' : Tm 1} {x : Atom} {h : x ∉ᶠ S}
      (q₀ : Conv (Γ ⨟ x ∶ A ∣ h) (b[x]) (b'[x]) B) (q₁ : x # (b, b')) :
      Conv Γ (𝛌 A b) (𝛌 A b') (A ⇒ B)
  /-- Agda: `App`. -/
  | app {S : Fset} {Γ : Cx S} {A B : Ty} {a a' b b' : Tm0}
      (q₀ : Conv Γ b b' (A ⇒ B)) (q₁ : Conv Γ a a' A) : Conv Γ (b ∙ a) (b' ∙ a') B
  /-- Agda: `Succ`. -/
  | succ {S : Fset} {Γ : Cx S} {a a' : Tm0} (q : Conv Γ a a' 𝐍𝐚𝐭) :
      Conv Γ (𝐬𝐮𝐜𝐜 a) (𝐬𝐮𝐜𝐜 a') 𝐍𝐚𝐭
  /-- Agda: `Nrec`. -/
  | nrec {S : Fset} {Γ : Cx S} {C : Ty} {c₀ c₀' cs cs' a a' : Tm0}
      (q₀ : Conv Γ c₀ c₀' C) (q₁ : Conv Γ cs cs' (𝐍𝐚𝐭 ⇒ C ⇒ C))
      (q₂ : Conv Γ a a' 𝐍𝐚𝐭) : Conv Γ (𝐧𝐫𝐞𝐜 c₀ cs a) (𝐧𝐫𝐞𝐜 c₀' cs' a') C
  /-- Agda: `BetaLam`. -/
  | betaLam {S : Fset} {Γ : Cx S} {A B : Ty} {a : Tm0} {b : Tm 1} {x : Atom}
      {h : x ∉ᶠ S} (q₀ : (Γ ⨟ x ∶ A ∣ h) ⊢ b[x] ∶ B) (q₁ : Γ ⊢ a ∶ A) (q₂ : x # b) :
      Conv Γ ((𝛌 A b) ∙ a) (b[a]) B
  /-- Agda: `BetaZero`. -/
  | betaZero {S : Fset} {Γ : Cx S} {C : Ty} {c₀ cs : Tm0} (q₀ : Γ ⊢ c₀ ∶ C)
      (q₁ : Γ ⊢ cs ∶ 𝐍𝐚𝐭 ⇒ C ⇒ C) : Conv Γ (𝐧𝐫𝐞𝐜 c₀ cs 𝐳𝐞𝐫𝐨) c₀ C
  /-- Agda: `BetaSucc`. -/
  | betaSucc {S : Fset} {Γ : Cx S} {C : Ty} {c₀ a cs : Tm0} (q₀ : Γ ⊢ c₀ ∶ C)
      (q₁ : Γ ⊢ cs ∶ 𝐍𝐚𝐭 ⇒ C ⇒ C) (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭) :
      Conv Γ (𝐧𝐫𝐞𝐜 c₀ cs (𝐬𝐮𝐜𝐜 a)) (cs ∙ a ∙ 𝐧𝐫𝐞𝐜 c₀ cs a) C
  /-- Agda: `Eta`. -/
  | eta {S : Fset} {Γ : Cx S} {A B : Ty} {b : Tm0} {x : Atom} (q₀ : Γ ⊢ b ∶ A ⇒ B)
      (q₁ : x # b) : Conv Γ b (𝛌 A (x ． b ∙ 𝐯x)) (A ⇒ B)

@[inherit_doc Conv]
scoped notation:25 Γ:26 " ⊢ " a:26 " ＝ " a':26 " ∶ " A:26 => GST.Conv Γ a a' A

/-! ## Transport along equalities

Lean-only plumbing for Agda's `subst`/`subst₂` on judgements. -/

/-- Transport a typing derivation along an equality of subjects. -/
def castTm {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} (e : a = a') (q : Γ ⊢ a ∶ A) :
    Γ ⊢ a' ∶ A := e ▸ q

/-- Transport a typing derivation along an equality of types. -/
def castTy {S : Fset} {Γ : Cx S} {A A' : Ty} {a : Tm0} (e : A = A') (q : Γ ⊢ a ∶ A) :
    Γ ⊢ a ∶ A' := e ▸ q

/-- Transport a conversion derivation along equalities of its two subjects. -/
def castEq {S : Fset} {Γ : Cx S} {A : Ty} {a a' b b' : Tm0} (e : a = a') (e' : b = b')
    (q : Γ ⊢ a ＝ b ∶ A) : Γ ⊢ a' ＝ b' ∶ A := e ▸ e' ▸ q

end GST

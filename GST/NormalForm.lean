import GST.UniqueTypes

/-!
# Normal and neutral forms

Port of `agda-code/agda/GST/NormalForm.agda`.

`Γ ⊢ⁿ a ∶ A` (`Nf`) and `Γ ⊢ᵘ a ∶ A` (`Ne`) are a mutual pair of `Type`-valued
inductive families, as in Agda: `GST/TypeSemantics.lean` builds the presheaves of
normal and of neutral forms from them, and `GST/TermSemantics.lean` recurses over the
`Nf` evidence of a numeral to define semantic `natrec`.
-/

namespace GST

open WSLN

/-! ## Normal and neutral forms -/

mutual

/-- Agda: `_⊢ⁿ_∶_` (GST/NormalForm.agda). -/
inductive Nf : {S : Fset} → Cx S → Tm0 → Ty → Type where
  /-- Agda: `Lam`. -/
  | lam {S : Fset} {Γ : Cx S} {A B : Ty} {b : Tm 1} {x : Atom} {h : x ∉ᶠ S}
      (q₀ : Nf (Γ ⨟ x ∶ A ∣ h) (b[x]) B) (q₁ : x # b) : Nf Γ (𝛌 A b) (A ⇒ B)
  /-- Agda: `Zero`. -/
  | zero {S : Fset} {Γ : Cx S} : Nf Γ 𝐳𝐞𝐫𝐨 𝐍𝐚𝐭
  /-- Agda: `Succ`. -/
  | succ {S : Fset} {Γ : Cx S} {a : Tm0} (q : Nf Γ a 𝐍𝐚𝐭) : Nf Γ (𝐬𝐮𝐜𝐜 a) 𝐍𝐚𝐭
  /-- Agda: `Neu`. -/
  | neu {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} (q : Ne Γ a A) : Nf Γ a A

/-- Agda: `_⊢ᵘ_∶_` (GST/NormalForm.agda). -/
inductive Ne : {S : Fset} → Cx S → Tm0 → Ty → Type where
  /-- Agda: `Var`. -/
  | var {S : Fset} {Γ : Cx S} {A : Ty} {x : Atom} (q : (x, A) isIn Γ) : Ne Γ (𝐯x) A
  /-- Agda: `App`. -/
  | app {S : Fset} {Γ : Cx S} {A B : Ty} {a b : Tm0} (q₀ : Ne Γ b (A ⇒ B))
      (q₁ : Nf Γ a A) : Ne Γ (b ∙ a) B
  /-- Agda: `Nrec`. -/
  | nrec {S : Fset} {Γ : Cx S} {C : Ty} {c₀ a cs : Tm0} (q₀ : Nf Γ c₀ C)
      (q₁ : Nf Γ cs (𝐍𝐚𝐭 ⇒ C ⇒ C)) (q₂ : Ne Γ a 𝐍𝐚𝐭) : Ne Γ (𝐧𝐫𝐞𝐜 c₀ cs a) C

end

@[inherit_doc Nf]
scoped notation:25 Γ:26 " ⊢ⁿ " a:26 " ∶ " A:26 => GST.Nf Γ a A

@[inherit_doc Ne]
scoped notation:25 Γ:26 " ⊢ᵘ " a:26 " ∶ " A:26 => GST.Ne Γ a A

/-- Transport a normal-form derivation along an equality of subjects. -/
def castNf {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} (e : a = a')
    (q : Γ ⊢ⁿ a ∶ A) : Γ ⊢ⁿ a' ∶ A := e ▸ q

/-- Transport a neutral-form derivation along an equality of subjects. -/
def castNe {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} (e : a = a')
    (q : Γ ⊢ᵘ a ∶ A) : Γ ⊢ᵘ a' ∶ A := e ▸ q

/-! ## Normal and neutral forms are typeable terms -/

mutual

/-- Agda: `tyⁿ` (GST/NormalForm.agda). -/
def nfDeriv {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} : (Γ ⊢ⁿ a ∶ A) → Γ ⊢ a ∶ A
  | .lam q₀ q₁ => .lam (nfDeriv q₀) q₁
  | .zero => .zero
  | .succ q => .succ (nfDeriv q)
  | .neu q => neDeriv q

/-- Agda: `tyᵘ` (GST/NormalForm.agda). -/
def neDeriv {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} : (Γ ⊢ᵘ a ∶ A) → Γ ⊢ a ∶ A
  | .var q => .var q
  | .app q₀ q₁ => .app (neDeriv q₀) (nfDeriv q₁)
  | .nrec q₀ q₁ q₂ => .nrec (nfDeriv q₀) (nfDeriv q₁) (neDeriv q₂)

end

/-! ## Renaming preserves normal and neutral forms -/

mutual

/-- Agda: `rn⊢ⁿ` (GST/NormalForm.agda). -/
def rnNf {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ : Rn} {A : Ty} {a : Tm0}
    (p : Γ' ⊢ʳ ρ ∶ Γ) : (Γ ⊢ⁿ a ∶ A) → Γ' ⊢ⁿ ρ * a ∶ A
  | .lam (A := A) (b := b) (x := x) (h := hx) q₀ q₁ =>
      let f := freshFor (ρ * b) (dom Γ')
      Nf.lam (A := A) (h := f.property.2)
        (castNf (rnUpdate_conc ρ x f.val b q₁)
          (rnNf (liftRn hx f.property.2 p) q₀))
        f.property.1
  | .zero => .zero
  | .succ q => .succ (rnNf p q)
  | .neu q => .neu (rnNe p q)

/-- Agda: `rn⊢ᵘ` (GST/NormalForm.agda). -/
def rnNe {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ : Rn} {A : Ty} {a : Tm0}
    (p : Γ' ⊢ʳ ρ ∶ Γ) : (Γ ⊢ᵘ a ∶ A) → Γ' ⊢ᵘ ρ * a ∶ A
  | .var q => .var (rnVar q p)
  | .app q₀ q₁ => .app (rnNe p q₀) (rnNf p q₁)
  | .nrec q₀ q₁ q₂ => .nrec (rnNf p q₀) (rnNf p q₁) (rnNe p q₂)

end

/-! ## Neutral substitutions -/

/-- Agda: `_⊢ˢᵘ_∶_` (GST/NormalForm.agda). -/
inductive NeSbTyping : {S' : Fset} → Cx S' → Sb sig → {S : Fset} → Cx S → Type where
  /-- Agda: `◇`. -/
  | nil {S' : Fset} {Γ' : Cx S'} {σ : Sb sig} : NeSbTyping Γ' σ ◇
  /-- Agda: `[]`. -/
  | snoc {S' S : Fset} {Γ' : Cx S'} {Γ : Cx S} {σ : Sb sig} {A : Ty} {x : Atom}
      {h : x ∉ᶠ S} (q₀ : NeSbTyping Γ' σ Γ) (q₁ : Γ' ⊢ᵘ σ x ∶ A) :
      NeSbTyping Γ' σ (Γ ⨟ x ∶ A ∣ h)

@[inherit_doc NeSbTyping]
scoped notation:25 Γ':26 " ⊢ˢᵘ " σ:41 " ∶ " Γ:41 => GST.NeSbTyping Γ' σ Γ

/-- Agda: `sbᵘ` (GST/NormalForm.agda). -/
def sbOfNeSb {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} :
    (Γ' ⊢ˢᵘ σ ∶ Γ) → Γ' ⊢ˢ σ ∶ Γ
  | .nil => .nil
  | .snoc q₀ q₁ => .snoc (sbOfNeSb q₀) (neDeriv q₁)

/-- Agda: `rnSbᵘ` (GST/NormalForm.agda). -/
def rnNeSb {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''} {ρ : Rn}
    {σ : Sb sig} (q : Γ'' ⊢ʳ ρ ∶ Γ') :
    (Γ' ⊢ˢᵘ σ ∶ Γ) → Γ'' ⊢ˢᵘ ((Sb.ofRn ρ : Sb sig) ∘ˢ σ) ∶ Γ
  | .nil => .nil
  | .snoc p₀ p₁ => .snoc (rnNeSb q p₀) (rnNe q p₁)

/-- Agda: `⊢ˢᵘExt` (GST/NormalForm.agda). -/
def neSbTypingExt {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig}
    (e : sbSetd (dom Γ) ∋ σ ~ σ') (p : Γ' ⊢ˢᵘ σ ∶ Γ) : Γ' ⊢ˢᵘ σ' ∶ Γ :=
  match p with
  | .nil => .nil
  | .snoc (x := x) q₀ q₁ =>
      .snoc (neSbTypingExt (fun y hy => e y (.unionL hy)) q₀)
        (castNe (e x (.unionR .single)) q₁)

/-- Agda: `wkSbᵘ` (GST/NormalForm.agda). -/
def wkNeSb {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A : Ty} {x : Atom}
    (h : x ∉ᶠ S') (q : Γ' ⊢ˢᵘ σ ∶ Γ) : (Γ' ⨟ x ∶ A ∣ h) ⊢ˢᵘ σ ∶ Γ :=
  neSbTypingExt (fun y _ => sbUnit (σ y)) (rnNeSb (wkRn h (rnTypingId Γ')) q)

/-- Agda: `[]ᵘ` (GST/NormalForm.agda). -/
def neSbTypingUpdate {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A : Ty}
    {a : Tm0} {x : Atom} (hx : x ∉ᶠ S) (q : Γ' ⊢ˢᵘ σ ∶ Γ) (qa : Γ' ⊢ᵘ a ∶ A) :
    Γ' ⊢ˢᵘ (σ ∘/ x ≔ a) ∶ (Γ ⨟ x ∶ A ∣ hx) :=
  .snoc (neSbTypingExt (sbUpdate_fresh σ hx) q) (castNe (Sb.update_eq σ x a).symm qa)

/-- Agda: `⊢ᵘidˢ` (GST/NormalForm.agda). -/
def neSbTypingId : {S : Fset} → (Γ : Cx S) → Γ ⊢ˢᵘ (Sb.id : Sb sig) ∶ Γ
  | _, .nil => .nil
  | _, .snoc Γ _ _ h => .snoc (wkNeSb h (neSbTypingId Γ)) (.var .new)

/-- Agda: `liftSbᵘ` (GST/NormalForm.agda). -/
def liftNeSb {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A : Ty} {x y : Atom}
    (hx : x ∉ᶠ S) (hy : y ∉ᶠ S') (q : Γ' ⊢ˢᵘ σ ∶ Γ) :
    (Γ' ⨟ y ∶ A ∣ hy) ⊢ˢᵘ (σ ∘/ x ≔ 𝐯y) ∶ (Γ ⨟ x ∶ A ∣ hx) :=
  neSbTypingUpdate hx (wkNeSb hy q) (.var .new)

/-- Agda: `ssbᵘ` (GST/NormalForm.agda). -/
def ssbNeSb {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} {x : Atom} (hx : x ∉ᶠ S)
    (q : Γ ⊢ᵘ a ∶ A) : Γ ⊢ˢᵘ (x ≔ a) ∶ (Γ ⨟ x ∶ A ∣ hx) :=
  neSbTypingUpdate hx (neSbTypingId Γ) q

/-- Agda: `⊢ᵘsbVar` (GST/NormalForm.agda). -/
def neSbVar {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {x : Atom} {A : Ty} :
    (x, A) isIn Γ → (Γ' ⊢ˢᵘ σ ∶ Γ) → Γ' ⊢ᵘ σ x ∶ A
  | .new, .snoc _ q => q
  | .old p, .snoc q _ => neSbVar p q

/-! ## Neutral substitution preserves normal and neutral forms -/

mutual

/-- Agda: `sb⊢ⁿ` (GST/NormalForm.agda). -/
def sbNf {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A : Ty} {a : Tm0}
    (p : Γ' ⊢ˢᵘ σ ∶ Γ) : (Γ ⊢ⁿ a ∶ A) → Γ' ⊢ⁿ σ * a ∶ A
  | .lam (A := A) (b := b) (x := x) (h := hx) q₀ q₁ =>
      let f := freshFor (σ * b) (dom Γ')
      Nf.lam (A := A) (h := f.property.2)
        (castNf (sbUpdate_conc σ x (𝐯f.val) b q₁)
          (sbNf (liftNeSb hx f.property.2 p) q₀))
        f.property.1
  | .zero => .zero
  | .succ q => .succ (sbNf p q)
  | .neu q => .neu (sbNe p q)

/-- Agda: `sb⊢ᵘ` (GST/NormalForm.agda). -/
def sbNe {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A : Ty} {a : Tm0}
    (p : Γ' ⊢ˢᵘ σ ∶ Γ) : (Γ ⊢ᵘ a ∶ A) → Γ' ⊢ᵘ σ * a ∶ A
  | .var (x := x) q =>
      castNe (Trm.weaken_self (σ x) (Nat.zero_le 0)).symm (neSbVar q p)
  | .app q₀ q₁ => .app (sbNe p q₀) (sbNf p q₁)
  | .nrec q₀ q₁ q₂ => .nrec (sbNf p q₀) (sbNf p q₁) (sbNe p q₂)

end

end GST

import GST.Renaming

/-!
# Well-typed substitutions

Port of `agda-code/agda/GST/Substitution.agda`.

Agda's mutually recursive `⊢ty₁`/`⊢ty₂` (reflexivity inversion) are one Lean
definition returning a pair, `convTy`, with the Agda names recovered as its two
projections; the mutual block is unnecessary that way, and the recursion stays
structural in the conversion derivation.
-/

namespace GST

open WSLN

/-! ## Well-typed and convertible substitutions -/

/-- Typed substitutions: `Δ ⊢ˢ σ ∶ Γ`. -/
inductive SbTyping : {S' : Fset} → Cx S' → Sb sig → {S : Fset} → Cx S → Type where
  | nil {S' : Fset} {Γ' : Cx S'} {σ : Sb sig} : SbTyping Γ' σ ◇
  | snoc {S' S : Fset} {Γ' : Cx S'} {Γ : Cx S} {σ : Sb sig} {A : Ty} {x : Atom}
      {h : x ∉ᶠ S} (q₀ : SbTyping Γ' σ Γ) (q₁ : Γ' ⊢ σ x ∶ A) :
      SbTyping Γ' σ (Γ ⨟ x ∶ A ∣ h)

@[inherit_doc SbTyping]
scoped notation:25 Γ':26 " ⊢ˢ " σ:41 " ∶ " Γ:41 => GST.SbTyping Γ' σ Γ

/-- Convertible substitutions: `Δ ⊢ˢ σ ＝ σ' ∶ Γ`. -/
inductive SbConv :
    {S' : Fset} → Cx S' → Sb sig → Sb sig → {S : Fset} → Cx S → Type where
  | nil {S' : Fset} {Γ' : Cx S'} {σ σ' : Sb sig} : SbConv Γ' σ σ' ◇
  | snoc {S' S : Fset} {Γ' : Cx S'} {Γ : Cx S} {σ σ' : Sb sig} {A : Ty} {x : Atom}
      {h : x ∉ᶠ S} (q₀ : SbConv Γ' σ σ' Γ) (q₁ : Γ' ⊢ σ x ＝ σ' x ∶ A) :
      SbConv Γ' σ σ' (Γ ⨟ x ∶ A ∣ h)

@[inherit_doc SbConv]
scoped notation:25 Γ':26 " ⊢ˢ " σ:41 " ＝ " σ':41 " ∶ " Γ:41 => GST.SbConv Γ' σ σ' Γ

def sbOfRnTyping {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ : Rn} :
    (Γ' ⊢ʳ ρ ∶ Γ) → Γ' ⊢ˢ (Sb.ofRn ρ : Sb sig) ∶ Γ
  | .nil => .nil
  | .snoc q₀ q₁ => .snoc (sbOfRnTyping q₀) (.var q₁)

/-- A typed renaming, viewed as a typed substitution. -/
abbrev rn2sb := @sbOfRnTyping

/-! ## Provable substitutions are well-scoped -/

theorem supp_sbTyping : {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {σ : Sb sig} →
    {x : Atom} → (Γ' ⊢ˢ σ ∶ Γ) → x ∈ dom Γ → supp (σ x) ⊆ dom Γ'
  | _, _, _, _, _, _, .nil, h => absurd h (Fset.not_mem_of_notMem .empty)
  | _, _, _, _, _, _, .snoc q₀ q₁, h => by
      cases h with
      | unionL h => exact supp_sbTyping q₀ h
      | unionR h => cases h; exact supp_deriv q₁

theorem supp_sbConv₁ : {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {σ σ' : Sb sig} →
    {x : Atom} → (Γ' ⊢ˢ σ ＝ σ' ∶ Γ) → x ∈ dom Γ → supp (σ x) ⊆ dom Γ'
  | _, _, _, _, _, _, _, .nil, h => absurd h (Fset.not_mem_of_notMem .empty)
  | _, _, _, _, _, _, _, .snoc q₀ q₁, h => by
      cases h with
      | unionL h => exact supp_sbConv₁ q₀ h
      | unionR h => cases h; exact supp_conv₁ q₁

theorem supp_sbConv₂ : {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {σ σ' : Sb sig} →
    {x : Atom} → (Γ' ⊢ˢ σ ＝ σ' ∶ Γ) → x ∈ dom Γ → supp (σ' x) ⊆ dom Γ'
  | _, _, _, _, _, _, _, .nil, h => absurd h (Fset.not_mem_of_notMem .empty)
  | _, _, _, _, _, _, _, .snoc q₀ q₁, h => by
      cases h with
      | unionL h => exact supp_sbConv₂ q₀ h
      | unionR h => cases h; exact supp_conv₂ q₁

/-! ## Renaming well-typed substitutions -/

def rnSb {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''} {ρ : Rn}
    {σ : Sb sig} (q : Γ'' ⊢ʳ ρ ∶ Γ') :
    (Γ' ⊢ˢ σ ∶ Γ) → Γ'' ⊢ˢ ((Sb.ofRn ρ : Sb sig) ∘ˢ σ) ∶ Γ
  | .nil => .nil
  | .snoc p₀ p₁ => .snoc (rnSb q p₀) (rnDeriv q p₁)

def rnSbConv {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''} {ρ : Rn}
    {σ₁ σ₂ : Sb sig} (q : Γ'' ⊢ʳ ρ ∶ Γ') :
    (Γ' ⊢ˢ σ₁ ＝ σ₂ ∶ Γ) →
      Γ'' ⊢ˢ ((Sb.ofRn ρ : Sb sig) ∘ˢ σ₁) ＝ ((Sb.ofRn ρ : Sb sig) ∘ˢ σ₂) ∶ Γ
  | .nil => .nil
  | .snoc p₀ p₁ => .snoc (rnSbConv q p₀) (rnConv q p₁)

/-! ## Setoid of substitutions in a given context -/

/-- The setoid of typed substitutions, `Sb[ Γ ]`. -/
def sbSetd (S : Fset) : Setd where
  El := Sb sig
  rel σ σ' := ∀ x, x ∈ S → σ x = σ' x
  rfl' _ _ _ := rfl
  symm' e x r := (e x r).symm
  trans' e e' x r := (e x r).trans (e' x r)

@[inherit_doc sbSetd] scoped notation:max "Sb[ " Γ " ]" => GST.sbSetd (GST.dom Γ)

theorem sbUpdate_fresh {S : Fset} {x : Atom} {a : Tm0} (σ : Sb sig) (h : x ∉ᶠ S) :
    sbSetd S ∋ σ ~ (σ ∘/ x ≔ a) := by
  intro y hy
  by_cases e : x = y
  · exact absurd (e ▸ hy) (Fset.not_mem_of_notMem h)
  · exact (Sb.update_neq σ a e).symm

/-! ## Extensionality properties of well-typed substitutions -/

def sbTypingExt {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig}
    (e : sbSetd (dom Γ) ∋ σ ~ σ') (p : Γ' ⊢ˢ σ ∶ Γ) : Γ' ⊢ˢ σ' ∶ Γ :=
  match p with
  | .nil => .nil
  | .snoc (x := x) q₀ q₁ =>
      .snoc (sbTypingExt (fun y hy => e y (.unionL hy)) q₀)
        (castTm (e x (.unionR .single)) q₁)

def sbConvExt {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' τ τ' : Sb sig}
    (e : sbSetd (dom Γ) ∋ σ ~ σ') (e' : sbSetd (dom Γ) ∋ τ ~ τ')
    (p : Γ' ⊢ˢ σ ＝ τ ∶ Γ) : Γ' ⊢ˢ σ' ＝ τ' ∶ Γ :=
  match p with
  | .nil => .nil
  | .snoc (x := x) q₀ q₁ =>
      .snoc (sbConvExt (fun y hy => e y (.unionL hy)) (fun y hy => e' y (.unionL hy)) q₀)
        (castEq (e x (.unionR .single)) (e' x (.unionR .single)) q₁)

def sbConvRefl {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} :
    (Γ' ⊢ˢ σ ∶ Γ) → Γ' ⊢ˢ σ ＝ σ ∶ Γ
  | .nil => .nil
  | .snoc p₀ p₁ => .snoc (sbConvRefl p₀) (.refl p₁)

def sbConvSymm {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig} :
    (Γ' ⊢ˢ σ ＝ σ' ∶ Γ) → Γ' ⊢ˢ σ' ＝ σ ∶ Γ
  | .nil => .nil
  | .snoc q₀ q₁ => .snoc (sbConvSymm q₀) (.symm q₁)

def sbConvTrans {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' σ'' : Sb sig} :
    (Γ' ⊢ˢ σ ＝ σ' ∶ Γ) → (Γ' ⊢ˢ σ' ＝ σ'' ∶ Γ) → Γ' ⊢ˢ σ ＝ σ'' ∶ Γ
  | .nil, .nil => .nil
  | .snoc q₀ q₁, .snoc q₀' q₁' => .snoc (sbConvTrans q₀ q₀') (.trans q₁ q₁')

def sbConvOfExt {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig}
    (e : sbSetd (dom Γ) ∋ σ ~ σ') (q : Γ' ⊢ˢ σ ∶ Γ) : Γ' ⊢ˢ σ ＝ σ' ∶ Γ :=
  sbConvExt (fun _ _ => rfl) e (sbConvRefl q)

def rnSbConv' {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''} {ρ ρ' : Rn}
    {σ₁ σ₂ : Sb sig} (q : Γ' ⊢ˢ σ₁ ＝ σ₂ ∶ Γ) (p : Γ'' ⊢ʳ ρ ∶ Γ')
    (e : rnSetd (dom Γ') ∋ ρ ~ ρ') :
    Γ'' ⊢ˢ ((Sb.ofRn ρ : Sb sig) ∘ˢ σ₁) ＝ ((Sb.ofRn ρ' : Sb sig) ∘ˢ σ₂) ∶ Γ :=
  sbConvExt (fun _ _ => rfl)
    (fun x r => rnRespSupp ρ ρ' (σ₂ x) fun y s => e y (supp_sbConv₂ q r s))
    (rnSbConv p q)

/-! ## Weakening -/

def wkSb {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A : Ty} {x : Atom}
    (h : x ∉ᶠ S') (q : Γ' ⊢ˢ σ ∶ Γ) : (Γ' ⨟ x ∶ A ∣ h) ⊢ˢ σ ∶ Γ :=
  sbTypingExt (fun y _ => sbUnit (σ y)) (rnSb (wkRn h (rnTypingId Γ')) q)

def wkSbConv {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig} {A : Ty} {x : Atom}
    (h : x ∉ᶠ S') (q : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) : (Γ' ⨟ x ∶ A ∣ h) ⊢ˢ σ ＝ σ' ∶ Γ :=
  sbConvExt (fun y _ => sbUnit (σ y)) (fun y _ => sbUnit (σ' y))
    (rnSbConv (wkRn h (rnTypingId Γ')) q)

/-! ## Lifting -/

def sbTypingUpdate {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A : Ty}
    {a : Tm0} {x : Atom} (hx : x ∉ᶠ S) (q : Γ' ⊢ˢ σ ∶ Γ) (qa : Γ' ⊢ a ∶ A) :
    Γ' ⊢ˢ (σ ∘/ x ≔ a) ∶ (Γ ⨟ x ∶ A ∣ hx) :=
  .snoc (sbTypingExt (sbUpdate_fresh σ hx) q)
    (castTm (Sb.update_eq σ x a).symm qa)

def sbConvUpdate {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig} {A : Ty}
    {a a' : Tm0} {x : Atom} (hx : x ∉ᶠ S) (q : Γ' ⊢ˢ σ ＝ σ' ∶ Γ)
    (qa : Γ' ⊢ a ＝ a' ∶ A) : Γ' ⊢ˢ (σ ∘/ x ≔ a) ＝ (σ' ∘/ x ≔ a') ∶ (Γ ⨟ x ∶ A ∣ hx) :=
  .snoc (sbConvExt (sbUpdate_fresh σ hx) (sbUpdate_fresh σ' hx) q)
    (castEq (Sb.update_eq σ x a).symm (Sb.update_eq σ' x a').symm qa)

def sbTypingUpdateFresh {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A : Ty}
    {a : Tm0} {x : Atom} (hx : x ∉ᶠ S) (q : Γ' ⊢ˢ σ ∶ Γ) (_ : Γ' ⊢ a ∶ A) :
    Γ' ⊢ˢ (σ ∘/ x ≔ a) ＝ σ ∶ Γ :=
  sbConvExt (sbUpdate_fresh σ hx) (fun _ _ => rfl) (sbConvRefl q)

def liftSb {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A : Ty} {x y : Atom}
    (hx : x ∉ᶠ S) (hy : y ∉ᶠ S') (q : Γ' ⊢ˢ σ ∶ Γ) :
    (Γ' ⨟ y ∶ A ∣ hy) ⊢ˢ (σ ∘/ x ≔ 𝐯y) ∶ (Γ ⨟ x ∶ A ∣ hx) :=
  sbTypingUpdate hx (wkSb hy q) (.var .new)

def liftSbConv {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig} {A : Ty}
    {x y : Atom} (hx : x ∉ᶠ S) (hy : y ∉ᶠ S') (q : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) :
    (Γ' ⨟ y ∶ A ∣ hy) ⊢ˢ (σ ∘/ x ≔ 𝐯y) ＝ (σ' ∘/ x ≔ 𝐯y) ∶ (Γ ⨟ x ∶ A ∣ hx) :=
  sbConvUpdate hx (wkSbConv hy q) (.refl (.var .new))

/-! ## The identity substitution -/

def sbTypingId : {S : Fset} → (Γ : Cx S) → Γ ⊢ˢ (Sb.id : Sb sig) ∶ Γ
  | _, .nil => .nil
  | _, .snoc Γ _ _ h => .snoc (wkSb h (sbTypingId Γ)) (.var .new)

def sbConvId {S : Fset} (Γ : Cx S) : Γ ⊢ˢ (Sb.id : Sb sig) ＝ Sb.id ∶ Γ :=
  sbConvRefl (sbTypingId Γ)

/-! ## Single substitution -/

def ssbTyping {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} {x : Atom} (hx : x ∉ᶠ S)
    (q : Γ ⊢ a ∶ A) : Γ ⊢ˢ (x ≔ a) ∶ (Γ ⨟ x ∶ A ∣ hx) :=
  sbTypingUpdate hx (sbTypingId Γ) q

def ssbConv {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} {x : Atom} (hx : x ∉ᶠ S)
    (q : Γ ⊢ a ＝ a' ∶ A) : Γ ⊢ˢ (x ≔ a) ＝ (x ≔ a') ∶ (Γ ⨟ x ∶ A ∣ hx) :=
  sbConvUpdate hx (sbConvId Γ) q

/-! ## Types of variables under substitution -/

def sbVar {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {x : Atom} {A : Ty} :
    (x, A) isIn Γ → (Γ' ⊢ˢ σ ∶ Γ) → Γ' ⊢ σ x ∶ A
  | .new, .snoc _ q => q
  | .old p, .snoc q _ => sbVar p q

def sbConvVar {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig} {x : Atom}
    {A : Ty} : (x, A) isIn Γ → (Γ' ⊢ˢ σ ＝ σ' ∶ Γ) → Γ' ⊢ σ x ＝ σ' x ∶ A
  | .new, .snoc _ q => q
  | .old p, .snoc q _ => sbConvVar p q

/-! ## Substitution preserves typing -/

def sbDeriv {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A : Ty} {a : Tm0}
    (p : Γ' ⊢ˢ σ ∶ Γ) : (Γ ⊢ a ∶ A) → Γ' ⊢ σ * a ∶ A
  | .var (x := x) q =>
      castTm (Trm.weaken_self (σ x) (Nat.zero_le 0)).symm (sbVar q p)
  | .lam (A := A) (b := b) (x := x) (h := hx) q₀ q₁ =>
      let f := freshFor (σ * b) (dom Γ')
      have hΓ' := f.property.2
      Deriv.lam (A := A) (h := hΓ')
        (castTm (sbUpdate_conc σ x (𝐯f.val) b q₁)
          (sbDeriv (liftSb hx hΓ' p) q₀))
        f.property.1
  | .app q₀ q₁ => .app (sbDeriv p q₀) (sbDeriv p q₁)
  | .zero => .zero
  | .succ q => .succ (sbDeriv p q)
  | .nrec q₀ q₁ q₂ => .nrec (sbDeriv p q₀) (sbDeriv p q₁) (sbDeriv p q₂)

def sbDerivBody {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A B : Ty}
    {x x' : Atom} (hx : x ∉ᶠ S) (hx' : x' ∉ᶠ S') (b : Tm 1) (p : Γ' ⊢ˢ σ ∶ Γ)
    (q : (Γ ⨟ x ∶ A ∣ hx) ⊢ b[x] ∶ B) (hb : x # b) :
    (Γ' ⨟ x' ∶ A ∣ hx') ⊢ (σ * b)[x'] ∶ B :=
  castTm (sbUpdate_conc σ x (𝐯x') b hb) (sbDeriv (liftSb hx hx' p) q)

/-! ## Substitution preserves conversion -/

def sbConv {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} {A : Ty} {a a' : Tm0}
    (p : Γ' ⊢ˢ σ ∶ Γ) : (Γ ⊢ a ＝ a' ∶ A) → Γ' ⊢ σ * a ＝ σ * a' ∶ A
  | .refl q => .refl (sbDeriv p q)
  | .symm q => .symm (sbConv p q)
  | .trans q₀ q₁ => .trans (sbConv p q₀) (sbConv p q₁)
  | .lam (A := A) (b := b) (b' := b') (x := x) (h := hx) q₀ q₁ =>
      let f := freshFor ((σ * b, σ * b') : Tm 1 × Tm 1) (dom Γ')
      have hΓ' := f.property.2
      Conv.lam (A := A) (h := hΓ')
        (castEq (sbUpdate_conc σ x (𝐯f.val) b (Fset.notMem_union_left q₁))
          (sbUpdate_conc σ x (𝐯f.val) b' (Fset.notMem_union_right q₁))
          (sbConv (liftSb hx hΓ' p) q₀))
        f.property.1
  | .app q₀ q₁ => .app (sbConv p q₀) (sbConv p q₁)
  | .succ q => .succ (sbConv p q)
  | .nrec q₀ q₁ q₂ => .nrec (sbConv p q₀) (sbConv p q₁) (sbConv p q₂)
  | .betaLam (A := A) (a := a) (b := b) (x := x) (h := hx) q₀ q₁ q₂ =>
      let f := freshFor (σ * b) (dom Γ')
      have hΓ' := f.property.2
      castEq rfl (sb_conc σ b a).symm
        (Conv.betaLam (A := A) (h := hΓ')
          (castTm (sbUpdate_conc σ x (𝐯f.val) b q₂) (sbDeriv (liftSb hx hΓ' p) q₀))
          (sbDeriv p q₁) f.property.1)
  | .betaZero q₀ q₁ => .betaZero (sbDeriv p q₀) (sbDeriv p q₁)
  | .betaSucc q₀ q₁ q₂ => .betaSucc (sbDeriv p q₀) (sbDeriv p q₁) (sbDeriv p q₂)
  | .eta (A := A) (b := b) (x := x) q₀ q₁ =>
      let f := freshFor (σ * b : Tm0) (dom Γ')
      have hb := f.property.1
      have hΓ' := f.property.2
      castEq rfl
        (by
          have key : σ * (x ． (b ∙ 𝐯x))
              = (f.val ． (σ ∘/ x ≔ (𝐯f.val : Tm0)) * (b ∙ 𝐯x)) :=
            sbAbs σ x f.val (b ∙ 𝐯x) (by
              intro y hy hne
              rw [supp_app, supp_vr] at hy
              cases hy with
              | unionL hy =>
                  exact Fset.subset_notMem (supp_sbTyping p (supp_deriv q₀ hy)) hΓ'
              | unionR hy =>
                  cases hy with
                  | unionL hy => cases hy; exact absurd rfl hne
                  | unionR hy => cases hy)
          have e₂ : (σ ∘/ x ≔ (𝐯f.val : Tm0)) * (b ∙ 𝐯x) = (σ * b) ∙ (𝐯f.val : Tm0) := by
            show ((σ ∘/ x ≔ (𝐯f.val : Tm0)) * b) ∙
              ((σ ∘/ x ≔ (𝐯f.val : Tm0)) * (𝐯x : Tm0)) = _
            rw [updateFresh σ x (𝐯f.val) b q₁]
            show (σ * b) ∙ ((σ ∘/ x ≔ (𝐯f.val : Tm0)) * (Trm.atom x : Tm0)) = _
            rw [updateEq]
          show 𝛌 A (f.val ． (σ * b) ∙ 𝐯f.val) = 𝛌 A (σ * (x ． b ∙ 𝐯x))
          rw [key, e₂])
        (Conv.eta (sbDeriv p q₀) hb)

def sbEqDeriv {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig} {A : Ty}
    {a : Tm0} (p : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) : (Γ ⊢ a ∶ A) → Γ' ⊢ σ * a ＝ σ' * a ∶ A
  | .var (x := x) q =>
      castEq (Trm.weaken_self (σ x) (Nat.zero_le 0)).symm
        (Trm.weaken_self (σ' x) (Nat.zero_le 0)).symm (sbConvVar q p)
  | .lam (A := A) (b := b) (x := x) (h := hx) q₀ q₁ =>
      let f := freshFor ((σ * b, σ' * b) : Tm 1 × Tm 1) (dom Γ')
      have hΓ' := f.property.2
      Conv.lam (A := A) (h := hΓ')
        (castEq (sbUpdate_conc σ x (𝐯f.val) b q₁)
          (sbUpdate_conc σ' x (𝐯f.val) b q₁)
          (sbEqDeriv (liftSbConv hx hΓ' p) q₀))
        f.property.1
  | .app q₀ q₁ => .app (sbEqDeriv p q₀) (sbEqDeriv p q₁)
  | .zero => .refl .zero
  | .succ q => .succ (sbEqDeriv p q)
  | .nrec q₀ q₁ q₂ => .nrec (sbEqDeriv p q₀) (sbEqDeriv p q₁) (sbEqDeriv p q₂)

/-! ## Concretion preserves typing -/

def concDeriv {S : Fset} {Γ : Cx S} {A B : Ty} {a : Tm0} (b : Tm 1) (x : Atom)
    (hx : x ∉ᶠ S) (p : (Γ ⨟ x ∶ A ∣ hx) ⊢ b[x] ∶ B) (q : Γ ⊢ a ∶ A) (hb : x # b) :
    Γ ⊢ b[a] ∶ B :=
  castTm (ssb_conc x a b hb) (sbDeriv (ssbTyping hx q) p)

/-! ## Reflexivity inversion -/

/-- Both typing derivations of a conversion, as one structural recursion. -/
def convTy {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} :
    (Γ ⊢ a ＝ a' ∶ A) → (Γ ⊢ a ∶ A) × (Γ ⊢ a' ∶ A)
  | .refl q => ⟨q, q⟩
  | .symm q => ((convTy q).2, (convTy q).1)
  | .trans q₀ q₁ => ((convTy q₀).1, (convTy q₁).2)
  | .lam q₀ q₁ =>
      ⟨.lam (convTy q₀).1 (Fset.notMem_union_left q₁),
       .lam (convTy q₀).2 (Fset.notMem_union_right q₁)⟩
  | .app q₀ q₁ =>
      ⟨.app (convTy q₀).1 (convTy q₁).1, .app (convTy q₀).2 (convTy q₁).2⟩
  | .succ q => ⟨.succ (convTy q).1, .succ (convTy q).2⟩
  | .nrec q₀ q₁ q₂ =>
      ⟨.nrec (convTy q₀).1 (convTy q₁).1 (convTy q₂).1,
       .nrec (convTy q₀).2 (convTy q₁).2 (convTy q₂).2⟩
  | .betaLam (b := b) (x := x) (h := hx) q₀ q₁ q₂ =>
      ⟨.app (.lam q₀ q₂) q₁, concDeriv b x hx q₀ q₁ q₂⟩
  | .betaZero q₀ q₁ => ⟨.nrec q₀ q₁ .zero, q₀⟩
  | .betaSucc q₀ q₁ q₂ => ⟨.nrec q₀ q₁ (.succ q₂), .app (.app q₁ q₂) (.nrec q₀ q₁ q₂)⟩
  | .eta (Γ := Γ) (A := A) (b := b) (x := x) q₀ q₁ =>
      ⟨q₀,
        let f := freshFor (x, b) (dom Γ)
        have hx' := Fset.notMem_union_left f.property.1
        have hb' := Fset.notMem_union_right f.property.1
        have hΓ := f.property.2
        Deriv.lam (A := A) (h := hΓ)
          (castTm
            (by
              show (b ∙ 𝐯f.val : Tm0) = (x ． b ∙ 𝐯x)[f.val]
              rw [conc_atom, ← conc_trm, concAbs x (b ∙ 𝐯x) (Trm.atom f.val)]
              show _ = ((x ≔ (𝐯f.val : Tm0)) * b) ∙ ((x ≔ (𝐯f.val : Tm0)) * (𝐯x : Tm0))
              rw [ssbFresh x (𝐯f.val) b q₁]
              show _ = b ∙ ((x ≔ (𝐯f.val : Tm0)) * (Trm.atom x : Tm0))
              rw [Sb.single_def x (𝐯f.val : Tm0), updateEq])
            (.app (wkDeriv hΓ q₀) (.var .new)))
          (fresh_abs' (b ∙ 𝐯x) (by
            show f.val ∉ᶠ supp b ∪ (｛ x ｝ ∪ ∅)
            exact .union hb' (.union hx' .empty)))⟩

def convTy₁ {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} (q : Γ ⊢ a ＝ a' ∶ A) :
    Γ ⊢ a ∶ A := (convTy q).1

def convTy₂ {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} (q : Γ ⊢ a ＝ a' ∶ A) :
    Γ ⊢ a' ∶ A := (convTy q).2

/-! ## Reflexivity inversion for substitutions -/

def sbConvTy₁ {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig} :
    (Γ' ⊢ˢ σ ＝ σ' ∶ Γ) → Γ' ⊢ˢ σ ∶ Γ
  | .nil => .nil
  | .snoc q₀ q₁ => .snoc (sbConvTy₁ q₀) (convTy₁ q₁)

def sbConvTy₂ {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig} :
    (Γ' ⊢ˢ σ ＝ σ' ∶ Γ) → Γ' ⊢ˢ σ' ∶ Γ
  | .nil => .nil
  | .snoc q₀ q₁ => .snoc (sbConvTy₂ q₀) (convTy₂ q₁)

/-! ## Substitution preserves conversion, continued -/

def sbEqConv {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig} {A : Ty}
    {a a' : Tm0} (p : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) (q : Γ ⊢ a ＝ a' ∶ A) :
    Γ' ⊢ σ * a ＝ σ' * a' ∶ A :=
  .trans (sbEqDeriv p (convTy₁ q)) (sbConv (sbConvTy₂ p) q)

def sbEqConvBody {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ σ' : Sb sig} {A B : Ty}
    {x x' : Atom} (hx : x ∉ᶠ S) (hx' : x' ∉ᶠ S') (b b' : Tm 1)
    (p : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) (q : (Γ ⨟ x ∶ A ∣ hx) ⊢ b[x] ＝ b'[x] ∶ B)
    (hb : x # (b, b')) : (Γ' ⨟ x' ∶ A ∣ hx') ⊢ (σ * b)[x'] ＝ (σ' * b')[x'] ∶ B :=
  castEq (sbUpdate_conc σ x (𝐯x') b (Fset.notMem_union_left hb))
    (sbUpdate_conc σ' x (𝐯x') b' (Fset.notMem_union_right hb))
    (sbEqConv (liftSbConv hx hx' p) q)

/-! ## Composing well-typed substitutions -/

def sbTypingComp {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''}
    {σ σ' : Sb sig} (q : Γ'' ⊢ˢ σ' ∶ Γ') : (Γ' ⊢ˢ σ ∶ Γ) → Γ'' ⊢ˢ (σ' ∘ˢ σ) ∶ Γ
  | .nil => .nil
  | .snoc p₀ p₁ => .snoc (sbTypingComp q p₀) (sbDeriv q p₁)

def sbConvComp {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''}
    {σ₁ σ₂ σ₁' σ₂' : Sb sig} (q : Γ'' ⊢ˢ σ₁' ＝ σ₂' ∶ Γ') :
    (Γ' ⊢ˢ σ₁ ＝ σ₂ ∶ Γ) → Γ'' ⊢ˢ (σ₁' ∘ˢ σ₁) ＝ (σ₂' ∘ˢ σ₂) ∶ Γ
  | .nil => .nil
  | .snoc p₀ p₁ => .snoc (sbConvComp q p₀) (sbEqConv q p₁)

/-! ## Unitary and associative laws -/

def sbUnitConv {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig}
    (q : Γ' ⊢ˢ σ ∶ Γ) : Γ' ⊢ˢ ((Sb.id : Sb sig) ∘ˢ σ) ＝ σ ∶ Γ :=
  sbConvSymm (sbConvOfExt (fun x _ => (sbUnit (σ x)).symm) q)

def sbAssocConv {S S' S'' S''' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''}
    {Γ''' : Cx S'''} {σ₁ σ₂ σ₃ : Sb sig} (q₃ : Γ''' ⊢ˢ σ₃ ∶ Γ'')
    (q₂ : Γ'' ⊢ˢ σ₂ ∶ Γ') (q₁ : Γ' ⊢ˢ σ₁ ∶ Γ) :
    Γ''' ⊢ˢ ((σ₃ ∘ˢ σ₂) ∘ˢ σ₁) ＝ (σ₃ ∘ˢ (σ₂ ∘ˢ σ₁)) ∶ Γ :=
  sbConvOfExt (fun x _ => sbAssoc σ₂ σ₃ (σ₁ x))
    (sbTypingComp (sbTypingComp q₃ q₂) q₁)

/-! ## Concretion preserves conversion -/

def concConv {S : Fset} {Γ : Cx S} {A B : Ty} {a a' : Tm0} (b b' : Tm 1) (x : Atom)
    (hx : x ∉ᶠ S) (p : (Γ ⨟ x ∶ A ∣ hx) ⊢ b[x] ＝ b'[x] ∶ B) (q : Γ ⊢ a ＝ a' ∶ A)
    (hb : x # (b, b')) : Γ ⊢ b[a] ＝ b'[a'] ∶ B :=
  castEq (ssb_conc x a b (Fset.notMem_union_left hb))
    (ssb_conc x a' b' (Fset.notMem_union_right hb))
    (sbEqConv (ssbConv hx q) p)

end GST

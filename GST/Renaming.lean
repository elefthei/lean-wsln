import GST.WellScoped
import GST.Setoid

/-!
# Well-typed renamings

Port of `agda-code/agda/GST/Renaming.agda`.

`Γ' ⊢ʳ ρ ∶ Γ` is `Type`-valued, as in Agda: `GST/TypeSemantics.lean` recurses over it
to reindex a semantic environment (`_⊚_`).

Agda's setoid of renamings `Rn[ Γ ]` only depends on `dom Γ`, so the port takes the
domain: `rnSetd S`.  The notation `Rn[ Γ ]` is retained and unfolds to `rnSetd (dom Γ)`.
-/

namespace GST

open WSLN

/-! ## Well-typed renaming -/

/-- Agda: `_⊢ʳ_∶_` (GST/Renaming.agda). -/
inductive RnTyping : {S' : Fset} → Cx S' → Rn → {S : Fset} → Cx S → Type where
  /-- Agda: `◇`. -/
  | nil {S' : Fset} {Γ' : Cx S'} {ρ : Rn} : RnTyping Γ' ρ ◇
  /-- Agda: `[]`. -/
  | snoc {S' S : Fset} {Γ' : Cx S'} {Γ : Cx S} {ρ : Rn} {A : Ty} {x : Atom}
      {h : x ∉ᶠ S} (q₀ : RnTyping Γ' ρ Γ) (q₁ : (ρ x, A) isIn Γ') :
      RnTyping Γ' ρ (Γ ⨟ x ∶ A ∣ h)

@[inherit_doc RnTyping]
scoped notation:25 Γ':26 " ⊢ʳ " ρ:41 " ∶ " Γ:41 => GST.RnTyping Γ' ρ Γ

/-- Agda: `[]₀` (GST/Renaming.agda). -/
def RnTyping.inv₀ {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ : Rn} {A : Ty} {x : Atom}
    {h : x ∉ᶠ S} (q : Γ' ⊢ʳ ρ ∶ (Γ ⨟ x ∶ A ∣ h)) : Γ' ⊢ʳ ρ ∶ Γ :=
  match q with
  | .snoc q₀ _ => q₀

/-- Agda: `[]₁` (GST/Renaming.agda). -/
def RnTyping.inv₁ {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ : Rn} {A : Ty} {x : Atom}
    {h : x ∉ᶠ S} (q : Γ' ⊢ʳ ρ ∶ (Γ ⨟ x ∶ A ∣ h)) : (ρ x, A) isIn Γ' :=
  match q with
  | .snoc _ q₁ => q₁

/-! ## Setoid of renamings of the variables in a given context -/

/-- Agda: `Rn[_]` (GST/Renaming.agda). -/
def rnSetd (S : Fset) : Setd where
  El := Rn
  rel ρ ρ' := ∀ x, x ∈ S → ρ x = ρ' x
  rfl' _ _ _ := rfl
  symm' e x r := (e x r).symm
  trans' e e' x r := (e x r).trans (e' x r)

@[inherit_doc rnSetd] scoped notation:max "Rn[ " Γ " ]" => GST.rnSetd (GST.dom Γ)

/-- Agda: `rnUpdate#` (GST/Renaming.agda). -/
theorem rnUpdate_fresh {S : Fset} {x x' : Atom} (ρ : Rn) (h : x ∉ᶠ S) :
    rnSetd S ∋ ρ ~ (ρ ∘/ x ≔ʳ x') := by
  intro y hy
  by_cases e : x = y
  · exact absurd (e ▸ hy) (Fset.not_mem_of_notMem h)
  · exact (Rn.update_neq ρ x' e).symm

/-! ## Renaming is well scoped -/

/-- Agda: `rnDom` (GST/Renaming.agda). -/
theorem rnDom : {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {ρ : Rn} → {x : Atom} →
    (Γ' ⊢ʳ ρ ∶ Γ) → x ∈ dom Γ → ρ x ∈ dom Γ'
  | _, _, _, _, _, _, .nil, h => absurd h (Fset.not_mem_of_notMem .empty)
  | _, _, _, _, _, _, .snoc q₀ q₁, h => by
      cases h with
      | unionL h => exact rnDom q₀ h
      | unionR h => cases h; exact isIn_dom q₁

/-- Agda: `Rn[]∘` (GST/Renaming.agda). -/
theorem rnSetd_comp {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ ρ' ρ₁ ρ₁' : Rn}
    (p : Γ' ⊢ʳ ρ ∶ Γ) (e : rnSetd (dom Γ) ∋ ρ ~ ρ')
    (e₁ : rnSetd (dom Γ') ∋ ρ₁ ~ ρ₁') :
    rnSetd (dom Γ) ∋ Rn.comp ρ₁ ρ ~ Rn.comp ρ₁' ρ' :=
  fun x r => (e₁ (ρ x) (rnDom p r)).trans (congrArg ρ₁' (e x r))

/-! ## Types of variables under renaming -/

/-- Agda: `⊢rnVar` (GST/Renaming.agda). -/
def rnVar {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ : Rn} {x : Atom} {A : Ty} :
    (x, A) isIn Γ → (Γ' ⊢ʳ ρ ∶ Γ) → (ρ x, A) isIn Γ'
  | .new, .snoc _ q₁ => q₁
  | .old q, .snoc p _ => rnVar q p

/-! ## Weakening, identity, composition and extensionality -/

/-- Agda: `wkRn` (GST/Renaming.agda). -/
def wkRn {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ : Rn} {A : Ty} {x : Atom}
    (h : x ∉ᶠ S') : (Γ' ⊢ʳ ρ ∶ Γ) → (Γ' ⨟ x ∶ A ∣ h) ⊢ʳ ρ ∶ Γ
  | .nil => .nil
  | .snoc q₀ q₁ => .snoc (wkRn h q₀) (.old q₁)

/-- Agda: `⊢ʳid` (GST/Renaming.agda). -/
def rnTypingId : {S : Fset} → (Γ : Cx S) → Γ ⊢ʳ Rn.id ∶ Γ
  | _, .nil => .nil
  | _, .snoc Γ _ _ h => .snoc (wkRn h (rnTypingId Γ)) .new

/-- Agda: `⊢ʳ∘` (GST/Renaming.agda). -/
def rnTypingComp {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''} {ρ ρ' : Rn}
    (p' : Γ'' ⊢ʳ ρ' ∶ Γ') : (Γ' ⊢ʳ ρ ∶ Γ) → Γ'' ⊢ʳ Rn.comp ρ' ρ ∶ Γ
  | .nil => .nil
  | .snoc (x := x) q₀ q₁ => .snoc (rnTypingComp p' q₀) (rnVar (x := ρ x) q₁ p')

/-- Agda: `⊢ʳExt` (GST/Renaming.agda). -/
def rnTypingExt {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ ρ' : Rn}
    (e : rnSetd (dom Γ) ∋ ρ ~ ρ') (p : Γ' ⊢ʳ ρ ∶ Γ) : Γ' ⊢ʳ ρ' ∶ Γ :=
  match p with
  | .nil => .nil
  | .snoc (x := x) q₀ q₁ =>
      .snoc (rnTypingExt (fun y hy => e y (.unionL hy)) q₀)
        (castIsIn (e x (.unionR .single)) q₁)

/-- Agda: `liftRn` (GST/Renaming.agda). -/
def liftRn {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ : Rn} {A : Ty} {x x' : Atom}
    (hx : x ∉ᶠ S) (hx' : x' ∉ᶠ S') (p : Γ' ⊢ʳ ρ ∶ Γ) :
    (Γ' ⨟ x' ∶ A ∣ hx') ⊢ʳ (ρ ∘/ x ≔ʳ x') ∶ (Γ ⨟ x ∶ A ∣ hx) :=
  .snoc (rnTypingExt (rnUpdate_fresh ρ hx) (wkRn hx' p))
    (castIsIn (Rn.update_eq ρ x x').symm .new)

/-! ## Renaming preserves typing -/

/-- Agda: `rn⊢` (GST/Renaming.agda). -/
def rnDeriv {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ : Rn} {A : Ty} {a : Tm0}
    (p : Γ' ⊢ʳ ρ ∶ Γ) : (Γ ⊢ a ∶ A) → Γ' ⊢ ρ * a ∶ A
  | .var q => .var (rnVar q p)
  | .lam (A := A) (b := b) (x := x) (h := hx) q₀ q₁ =>
      let f := freshFor (ρ * b) (dom Γ')
      Deriv.lam (A := A) (h := f.property.2)
        (castTm (rnUpdate_conc ρ x f.val b q₁)
          (rnDeriv (liftRn hx f.property.2 p) q₀))
        f.property.1
  | .app q₀ q₁ => .app (rnDeriv p q₀) (rnDeriv p q₁)
  | .zero => .zero
  | .succ q => .succ (rnDeriv p q)
  | .nrec q₀ q₁ q₂ => .nrec (rnDeriv p q₀) (rnDeriv p q₁) (rnDeriv p q₂)

/-- Agda: `rn⊢¹` (GST/Renaming.agda): the λ-body typing is independent of the choice
of fresh concreting atom. -/
def rnDerivBody {S : Fset} {Γ : Cx S} {A B : Ty} (x x' : Atom) (hx : x ∉ᶠ S)
    (hx' : x' ∉ᶠ S) (b : Tm 1) (q : (Γ ⨟ x ∶ A ∣ hx) ⊢ b[x] ∶ B) (hb : x # b)
    (_hb' : x' # b) : (Γ ⨟ x' ∶ A ∣ hx') ⊢ b[x'] ∶ B :=
  castTm (by rw [rnUpdate_conc (Sg := sig) Rn.id x x' b hb, rnUnit])
    (rnDeriv (liftRn hx hx' (rnTypingId Γ)) q)

/-! ## Renaming preserves conversion -/

/-- Agda: `rn＝` (GST/Renaming.agda). -/
def rnConv {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {ρ : Rn} {A : Ty} {a a' : Tm0}
    (p : Γ' ⊢ʳ ρ ∶ Γ) : (Γ ⊢ a ＝ a' ∶ A) → Γ' ⊢ ρ * a ＝ ρ * a' ∶ A
  | .refl q => .refl (rnDeriv p q)
  | .symm q => .symm (rnConv p q)
  | .trans q₀ q₁ => .trans (rnConv p q₀) (rnConv p q₁)
  | .lam (A := A) (b := b) (b' := b') (x := x) (h := hx) q₀ q₁ =>
      let f := freshFor ((ρ * b, ρ * b') : Tm 1 × Tm 1) (dom Γ')
      have hΓ' := f.property.2
      Conv.lam (A := A) (h := hΓ')
        (castEq (rnUpdate_conc ρ x f.val b (Fset.notMem_union_left q₁))
          (rnUpdate_conc ρ x f.val b' (Fset.notMem_union_right q₁))
          (rnConv (liftRn hx hΓ' p) q₀))
        f.property.1
  | .app q₀ q₁ => .app (rnConv p q₀) (rnConv p q₁)
  | .succ q => .succ (rnConv p q)
  | .nrec q₀ q₁ q₂ => .nrec (rnConv p q₀) (rnConv p q₁) (rnConv p q₂)
  | .betaLam (A := A) (a := a) (b := b) (x := x) (h := hx) q₀ q₁ q₂ =>
      let f := freshFor (ρ * b) (dom Γ')
      have hΓ' := f.property.2
      castEq rfl (rn_conc ρ b a).symm
        (Conv.betaLam (A := A) (h := hΓ')
          (castTm (rnUpdate_conc ρ x f.val b q₂)
            (rnDeriv (liftRn hx hΓ' p) q₀))
          (rnDeriv p q₁) f.property.1)
  | .betaZero q₀ q₁ => .betaZero (rnDeriv p q₀) (rnDeriv p q₁)
  | .betaSucc q₀ q₁ q₂ => .betaSucc (rnDeriv p q₀) (rnDeriv p q₁) (rnDeriv p q₂)
  | .eta (A := A) (b := b) (x := x) q₀ q₁ =>
      let f := freshFor (ρ * b : Tm0) (dom Γ')
      have hb := f.property.1
      have hΓ' := f.property.2
      castEq rfl
        (by
          have key : ρ * (x ． (b ∙ 𝐯x)) = (f.val ． ((ρ ∘/ x ≔ʳ f.val) : Rn) * (b ∙ 𝐯x)) :=
            rnAbs ρ x f.val (b ∙ 𝐯x) (by
              intro y hy hne e
              rw [supp_app, supp_vr] at hy
              cases hy with
              | unionL hy =>
                  exact Fset.not_mem_of_notMem hΓ'
                    (e ▸ rnDom p (supp_deriv q₀ hy))
              | unionR hy =>
                  cases hy with
                  | unionL hy => cases hy; exact hne rfl
                  | unionR hy => cases hy)
          have e₂ : ((ρ ∘/ x ≔ʳ f.val) : Rn) * (b ∙ 𝐯x) = (ρ * b) ∙ (𝐯f.val : Tm0) := by
            show (((ρ ∘/ x ≔ʳ f.val) : Rn) * b) ∙
              (((ρ ∘/ x ≔ʳ f.val) : Rn) * (𝐯x : Tm0)) = _
            rw [updateFreshRn ρ x f.val b q₁]
            show (ρ * b) ∙ (𝐯((ρ ∘/ x ≔ʳ f.val) x) : Tm0) = _
            rw [Rn.update_eq]
          show 𝛌 A (f.val ． (ρ * b) ∙ 𝐯f.val) = 𝛌 A (ρ * (x ． b ∙ 𝐯x))
          rw [key, e₂])
        (Conv.eta (rnDeriv p q₀) hb)

/-- Agda: `rn＝¹` (GST/Renaming.agda). -/
def rnConvBody {S : Fset} {Γ : Cx S} {A B : Ty} (x x' : Atom) (hx : x ∉ᶠ S)
    (hx' : x' ∉ᶠ S) (b b' : Tm 1) (q : (Γ ⨟ x ∶ A ∣ hx) ⊢ b[x] ＝ b'[x] ∶ B)
    (hb : x # (b, b')) (_hb' : x' # (b, b')) :
    (Γ ⨟ x' ∶ A ∣ hx') ⊢ b[x'] ＝ b'[x'] ∶ B :=
  castEq
    (by rw [rnUpdate_conc (Sg := sig) Rn.id x x' b (Fset.notMem_union_left hb), rnUnit])
    (by rw [rnUpdate_conc (Sg := sig) Rn.id x x' b' (Fset.notMem_union_right hb),
          rnUnit])
    (rnConv (liftRn hx hx' (rnTypingId Γ)) q)

/-! ## Weakening -/

/-- Agda: `wk⊢` (GST/Renaming.agda). -/
def wkDeriv {S : Fset} {Γ : Cx S} {A A' : Ty} {a : Tm0} {x : Atom} (h : x ∉ᶠ S)
    (q : Γ ⊢ a ∶ A) : (Γ ⨟ x ∶ A' ∣ h) ⊢ a ∶ A :=
  castTm (rnUnit a) (rnDeriv (wkRn h (rnTypingId Γ)) q)

/-- Agda: `wk＝` (GST/Renaming.agda). -/
def wkConv {S : Fset} {Γ : Cx S} {A A' : Ty} {a a' : Tm0} {x : Atom} (h : x ∉ᶠ S)
    (q : Γ ⊢ a ＝ a' ∶ A) : (Γ ⨟ x ∶ A' ∣ h) ⊢ a ＝ a' ∶ A :=
  castEq (rnUnit a) (rnUnit a') (rnConv (wkRn h (rnTypingId Γ)) q)

/-! ## Support-respecting renaming of terms -/

/-- Agda: `rnRespSuppTm` (GST/Renaming.agda). -/
def rnRespSuppTm {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {A : Ty} {a a' : Tm0}
    {ρ ρ' : Rn} (q : Γ ⊢ a ＝ a' ∶ A) (p : Γ' ⊢ʳ ρ ∶ Γ)
    (e : rnSetd (dom Γ) ∋ ρ ~ ρ') : Γ' ⊢ ρ * a ＝ ρ' * a' ∶ A :=
  castEq rfl (rnRespSupp ρ ρ' a' fun x hx => e x (supp_conv₂ q hx)) (rnConv p q)

/-! ## Unitary and associative laws -/

/-- Agda: `⊢rnUnit` (GST/Renaming.agda). -/
def rnUnitConv {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} (q : Γ ⊢ a ∶ A) :
    Γ ⊢ Rn.id * a ＝ a ∶ A := castEq (rnUnit a).symm rfl (.refl q)

/-- Agda: `⊢rnAssoc` (GST/Renaming.agda). -/
def rnAssocConv {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''} {A : Ty}
    {a : Tm0} {ρ ρ' : Rn} (q : Γ ⊢ a ∶ A) (p : Γ' ⊢ʳ ρ ∶ Γ) (p' : Γ'' ⊢ʳ ρ' ∶ Γ') :
    Γ'' ⊢ Rn.comp ρ' ρ * a ＝ ρ' * (ρ * a) ∶ A :=
  castEq (rnAssoc ρ ρ' a).symm rfl (.refl (rnDeriv p' (rnDeriv p q)))

end GST

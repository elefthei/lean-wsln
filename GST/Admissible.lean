import GST.Substitution

/-!
# Admissible rules

Port of `agda-code/agda/GST/Admissible.agda`.

Agda's `∑[ B ] (C ≡ A ⇒ B) ∧ (…)` mixes a proposition and a derivation, so `Lam⁻¹`
returns a `Sigma` of a `PProd` here: the type equation is a `Prop`, the derivation is
data, and `GST/DecidableConv.lean` needs both computationally.
-/

namespace GST

open WSLN

/-! ## Alternative form of congruence for λ-abstraction -/

/-- Agda: `Lam'` (GST/Admissible.agda). -/
def lam' {S : Fset} {Γ : Cx S} {A B : Ty} {b b' : Tm0} {x : Atom} (hx : x ∉ᶠ S)
    (q : (Γ ⨟ x ∶ A ∣ hx) ⊢ b ＝ b' ∶ B) :
    Γ ⊢ 𝛌 A (x ． b) ＝ 𝛌 A (x ． b') ∶ A ⇒ B :=
  Conv.lam (castEq (concAbs' x b).symm (concAbs' x b').symm q)
    (.union (fresh_abs x b) (fresh_abs x b'))

/-! ## Alternative form of the β-rule -/

/-- Agda: `BetaLam'` (GST/Admissible.agda). -/
def betaLam' {S : Fset} {Γ : Cx S} {A A' B : Ty} {a : Tm0} {b : Tm 1}
    (q : Γ ⊢ 𝛌 A' b ∶ A ⇒ B) (q' : Γ ⊢ a ∶ A) (_ : A = A') :
    Γ ⊢ (𝛌 A b) ∙ a ＝ b[a] ∶ B :=
  match q with
  | .lam q₀ q₁ => .betaLam q₀ q' q₁

/-! ## Inverse of the typing rule for λ-abstractions -/

/-- Agda: `Lam⁻¹` (GST/Admissible.agda). -/
def lamInv {S : Fset} {Γ : Cx S} {A C : Ty} {b : Tm 1} {x : Atom} (hx : x ∉ᶠ S)
    (q₀ : Γ ⊢ 𝛌 A b ∶ C) (q₁ : x # b) :
    Σ B : Ty, PProd (C = A ⇒ B) ((Γ ⨟ x ∶ A ∣ hx) ⊢ b[x] ∶ B) :=
  match q₀ with
  | .lam (x := x') (h := hx') q q₃ =>
      ⟨_, rfl, rnDerivBody x' x hx' hx b q q₃ q₁⟩

end GST

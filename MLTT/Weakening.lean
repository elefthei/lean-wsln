import MLTT.WellScoped

/-!
# Weakening

Port of `agda-code/agda/MLTT/Weakening.agda`.

`wkId` recurses on the context rather than on `Ok` itself, because `Ok` and `Deriv`
are one mutual family and Lean's `induction` tactic needs the joint recursor for it;
the recursion is the same one Agda performs.  `wkDeriv` is the exhaustive induction
over all thirty `Deriv` constructors, generalised over the weakened context, with the
binder cases enlarging the cofinite exclusion set to `S ∪ supp Δ` exactly as in Agda.
-/

namespace MLTT

open WSLN
open Fset

/-! ## Identity weakening -/

/-- Agda: `▷id` (MLTT/Weakening.agda). -/
theorem wkId {Γ : Cx} (p : Ok Γ) : Γ ▷ Γ := by
  revert p
  induction Γ with
  | nil => intro _; exact .nil
  | snoc Γ' x A l ih =>
      intro p
      cases p with
      | snoc q₀ q₁ hh => exact .snoc (ih hh) q₀ q₁ q₀

/-- Agda: `proj` (MLTT/Weakening.agda), renamed: `Weakens.proj` already has that name. -/
theorem wkProj {l : Lvl} {Γ : Cx} {A : Ty0} {x : Atom} (q : Γ ⊢ A ⦂ l) (q' : x # Γ) :
    (Γ ⨟ x ∶ A ⦂ l) ▷ Γ :=
  .proj (wkId (derivOk q)) q q'

/-! ## Types of variables under weakening -/

/-- Agda: `▷Var` (MLTT/Weakening.agda). -/
theorem wkVar {l : Lvl} {Δ Γ : Cx} {x : Atom} {A : Ty0} (p : Δ ▷ Γ)
    (q : (x, A, l) isIn Γ) : (x, A, l) isIn Δ := by
  revert q
  induction p with
  | nil => intro q; cases q
  | proj _ _ _ ih => intro q; exact .old (ih q)
  | snoc _ _ _ _ ih =>
      intro q
      cases q with
      | new => exact .new
      | old q' => exact .old (ih q')

/-! ## Weakening preserves provable judgements -/

/-- Agda: `▷Jg` (MLTT/Weakening.agda). -/
theorem wkDeriv {Δ Γ : Cx} {J : Jg} (p : Δ ▷ Γ) (q : Γ ⊢ J) : Δ ⊢ J := by
  revert Δ
  induction q using Deriv.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc _ _ _ _ _ => trivial
  | conv q₀ q₁ ih₀ ih₁ =>
      intro Δ p
      exact .conv (ih₀ p) (ih₁ p)
  | var q₀ q₁ ih =>
      intro Δ p
      exact .var (okWk p) (wkVar p q₁)
  | univ q ih =>
      intro Δ p
      exact .univ (okWk p)
  | pi S q₀ q₁ ih₀ ih₁ =>
      intro Δ p
      exact .pi (S ∪ supp Δ) (ih₀ p)
        (fun x hx => ih₁ x (notMem_union_left hx)
          (.snoc p q₀ (notMem_union_right hx) (ih₀ p)))
  | lam S q₀ h₀ h₁ ih₀ ih₁ ih₂ =>
      intro Δ p
      exact .lam (S ∪ supp Δ)
        (fun x hx => ih₀ x (notMem_union_left hx)
          (.snoc p h₀ (notMem_union_right hx) (ih₁ p)))
        (ih₁ p)
        (fun x hx => ih₂ x (notMem_union_left hx)
          (.snoc p h₀ (notMem_union_right hx) (ih₁ p)))
  | app S q₀ q₁ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      intro Δ p
      exact .app (S ∪ supp Δ) (ih₀ p) (ih₁ p)
        (fun x hx => ih₂ x (notMem_union_left hx)
          (.snoc p h (notMem_union_right hx) (ih₃ p)))
        (ih₃ p)
  | idF q₀ q₁ h ih₀ ih₁ ih₂ =>
      intro Δ p
      exact .idF (ih₀ p) (ih₁ p) (ih₂ p)
  | reflI q h ih₀ ih₁ =>
      intro Δ p
      exact .reflI (ih₀ p) (ih₁ p)
  | j S q₀ q₁ q₂ q₃ q₄ h₀ h₁ ih₀ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
      intro Δ p
      refine .j (S ∪ supp Δ) ?_ (ih₁ p) (ih₂ p) (ih₃ p) (ih₄ p) (ih₅ p)
        (fun x hx => ih₆ x (notMem_union_left hx)
          (.snoc p h₀ (notMem_union_right hx) (ih₅ p)))
      intro x y hfr
      obtain ⟨hy, hxx, hxy⟩ := fresh₂Inv hfr
      have hxS : x # S := notMem_union_left hxx
      have hxΔ : x # Δ := notMem_union_right hxx
      have hyS : y # S := notMem_union_left hy
      have hyΔ : y # Δ := notMem_union_right hy
      have pw := Weakens.snoc p h₀ hxΔ (ih₅ p)
      exact ih₀ x y (fresh₂Intro hyS hxS hxy)
        (.snoc pw (h₁ x hxS) (NotMem.union hyΔ (fresh_symm hxy)) (ih₆ x hxS pw))
  | nat q ih =>
      intro Δ p
      exact .nat (okWk p)
  | zero q ih =>
      intro Δ p
      exact .zero (okWk p)
  | succ q ih =>
      intro Δ p
      exact .succ (ih p)
  | nrec S q₀ q₁ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      intro Δ p
      refine .nrec (S ∪ supp Δ) (ih₀ p) ?_ (ih₂ p)
        (fun x hx => ih₃ x (notMem_union_left hx)
          (.snoc p (Deriv.nat (derivOk q₂)) (notMem_union_right hx)
            (Deriv.nat (okWk p))))
      intro x y hfr
      obtain ⟨hy, hxx, hxy⟩ := fresh₂Inv hfr
      have hxS : x # S := notMem_union_left hxx
      have hxΔ : x # Δ := notMem_union_right hxx
      have hyS : y # S := notMem_union_left hy
      have hyΔ : y # Δ := notMem_union_right hy
      have pw := Weakens.snoc p (Deriv.nat (derivOk q₂)) hxΔ (Deriv.nat (okWk p))
      exact ih₁ x y (fresh₂Intro hyS hxS hxy)
        (.snoc pw (h x hxS) (NotMem.union hyΔ (fresh_symm hxy)) (ih₃ x hxS pw))
  | refl q ih =>
      intro Δ p
      exact .refl (ih p)
  | symm q ih =>
      intro Δ p
      exact .symm (ih p)
  | trans q₀ q₁ ih₀ ih₁ =>
      intro Δ p
      exact .trans (ih₀ p) (ih₁ p)
  | eqConv q₀ q₁ ih₀ ih₁ =>
      intro Δ p
      exact .eqConv (ih₀ p) (ih₁ p)
  | piCong S q₀ q₁ h ih₀ ih₁ ih₂ =>
      intro Δ p
      exact .piCong (S ∪ supp Δ) (ih₀ p)
        (fun x hx => ih₁ x (notMem_union_left hx)
          (.snoc p h (notMem_union_right hx) (ih₂ p)))
        (ih₂ p)
  | lamCong S q₀ q₁ h₀ h₁ ih₀ ih₁ ih₂ ih₃ =>
      intro Δ p
      exact .lamCong (S ∪ supp Δ) (ih₀ p)
        (fun x hx => ih₁ x (notMem_union_left hx)
          (.snoc p h₀ (notMem_union_right hx) (ih₂ p)))
        (ih₂ p)
        (fun x hx => ih₃ x (notMem_union_left hx)
          (.snoc p h₀ (notMem_union_right hx) (ih₂ p)))
  | appCong S q₀ q₁ q₂ q₃ h₀ h₁ ih₀ ih₁ ih₂ ih₃ ih₄ ih₅ =>
      intro Δ p
      exact .appCong (S ∪ supp Δ) (ih₀ p)
        (fun x hx => ih₁ x (notMem_union_left hx)
          (.snoc p h₀ (notMem_union_right hx) (ih₄ p)))
        (ih₂ p) (ih₃ p) (ih₄ p)
        (fun x hx => ih₅ x (notMem_union_left hx)
          (.snoc p h₀ (notMem_union_right hx) (ih₄ p)))
  | idCong q₀ q₁ q₂ ih₀ ih₁ ih₂ =>
      intro Δ p
      exact .idCong (ih₀ p) (ih₁ p) (ih₂ p)
  | reflCong q h ih₀ ih₁ =>
      intro Δ p
      exact .reflCong (ih₀ p) (ih₁ p)
  | jCong S q₀ q₁ q₂ q₃ q₄ h₀ h₁ ih₀ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
      intro Δ p
      refine .jCong (S ∪ supp Δ) ?_ (ih₁ p) (ih₂ p) (ih₃ p) (ih₄ p) (ih₅ p)
        (fun x hx => ih₆ x (notMem_union_left hx)
          (.snoc p h₀ (notMem_union_right hx) (ih₅ p)))
      intro x y hfr
      obtain ⟨hy, hxx, hxy⟩ := fresh₂Inv hfr
      have hxS : x # S := notMem_union_left hxx
      have hxΔ : x # Δ := notMem_union_right hxx
      have hyS : y # S := notMem_union_left hy
      have hyΔ : y # Δ := notMem_union_right hy
      have pw := Weakens.snoc p h₀ hxΔ (ih₅ p)
      exact ih₀ x y (fresh₂Intro hyS hxS hxy)
        (.snoc pw (h₁ x hxS) (NotMem.union hyΔ (fresh_symm hxy)) (ih₆ x hxS pw))
  | succCong q ih =>
      intro Δ p
      exact .succCong (ih p)
  | nrecCong S q₀ q₁ q₂ q₃ h ih₀ ih₁ ih₂ ih₃ ih₄ =>
      intro Δ p
      refine .nrecCong (S ∪ supp Δ)
        (fun x hx => ih₀ x (notMem_union_left hx)
          (.snoc p (Deriv.nat (derivOk q₃)) (notMem_union_right hx)
            (Deriv.nat (okWk p))))
        (ih₁ p) ?_ (ih₃ p)
        (fun x hx => ih₄ x (notMem_union_left hx)
          (.snoc p (Deriv.nat (derivOk q₃)) (notMem_union_right hx)
            (Deriv.nat (okWk p))))
      intro x y hfr
      obtain ⟨hy, hxx, hxy⟩ := fresh₂Inv hfr
      have hxS : x # S := notMem_union_left hxx
      have hxΔ : x # Δ := notMem_union_right hxx
      have hyS : y # S := notMem_union_left hy
      have hyΔ : y # Δ := notMem_union_right hy
      have pw := Weakens.snoc p (Deriv.nat (derivOk q₃)) hxΔ (Deriv.nat (okWk p))
      exact ih₂ x y (fresh₂Intro hyS hxS hxy)
        (.snoc pw (h x hxS) (NotMem.union hyΔ (fresh_symm hxy)) (ih₄ x hxS pw))
  | piBeta S q₀ q₁ h₀ h₁ ih₀ ih₁ ih₂ ih₃ =>
      intro Δ p
      exact .piBeta (S ∪ supp Δ)
        (fun x hx => ih₀ x (notMem_union_left hx)
          (.snoc p h₀ (notMem_union_right hx) (ih₂ p)))
        (ih₁ p) (ih₂ p)
        (fun x hx => ih₃ x (notMem_union_left hx)
          (.snoc p h₀ (notMem_union_right hx) (ih₂ p)))
  | idBeta S q₀ q₁ q₂ h₀ h₁ ih₀ ih₁ ih₂ ih₃ ih₄ =>
      intro Δ p
      refine .idBeta (S ∪ supp Δ) ?_ (ih₁ p) (ih₂ p) (ih₃ p)
        (fun x hx => ih₄ x (notMem_union_left hx)
          (.snoc p h₀ (notMem_union_right hx) (ih₃ p)))
      intro x y hfr
      obtain ⟨hy, hxx, hxy⟩ := fresh₂Inv hfr
      have hxS : x # S := notMem_union_left hxx
      have hxΔ : x # Δ := notMem_union_right hxx
      have hyS : y # S := notMem_union_left hy
      have hyΔ : y # Δ := notMem_union_right hy
      have pw := Weakens.snoc p h₀ hxΔ (ih₃ p)
      exact ih₀ x y (fresh₂Intro hyS hxS hxy)
        (.snoc pw (h₁ x hxS) (NotMem.union hyΔ (fresh_symm hxy)) (ih₄ x hxS pw))
  | natBeta₀ S q₀ q₁ h ih₀ ih₁ ih₂ =>
      intro Δ p
      refine .natBeta₀ (S ∪ supp Δ) (ih₀ p) ?_
        (fun x hx => ih₂ x (notMem_union_left hx)
          (.snoc p (Deriv.nat (derivOk q₀)) (notMem_union_right hx)
            (Deriv.nat (okWk p))))
      intro x y hfr
      obtain ⟨hy, hxx, hxy⟩ := fresh₂Inv hfr
      have hxS : x # S := notMem_union_left hxx
      have hxΔ : x # Δ := notMem_union_right hxx
      have hyS : y # S := notMem_union_left hy
      have hyΔ : y # Δ := notMem_union_right hy
      have pw := Weakens.snoc p (Deriv.nat (derivOk q₀)) hxΔ (Deriv.nat (okWk p))
      exact ih₁ x y (fresh₂Intro hyS hxS hxy)
        (.snoc pw (h x hxS) (NotMem.union hyΔ (fresh_symm hxy)) (ih₂ x hxS pw))
  | natBetaS S q₀ q₁ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      intro Δ p
      refine .natBetaS (S ∪ supp Δ) (ih₀ p) ?_ (ih₂ p)
        (fun x hx => ih₃ x (notMem_union_left hx)
          (.snoc p (Deriv.nat (derivOk q₀)) (notMem_union_right hx)
            (Deriv.nat (okWk p))))
      intro x y hfr
      obtain ⟨hy, hxx, hxy⟩ := fresh₂Inv hfr
      have hxS : x # S := notMem_union_left hxx
      have hxΔ : x # Δ := notMem_union_right hxx
      have hyS : y # S := notMem_union_left hy
      have hyΔ : y # Δ := notMem_union_right hy
      have pw := Weakens.snoc p (Deriv.nat (derivOk q₀)) hxΔ (Deriv.nat (okWk p))
      exact ih₁ x y (fresh₂Intro hyS hxS hxy)
        (.snoc pw (h x hxS) (NotMem.union hyΔ (fresh_symm hxy)) (ih₃ x hxS pw))
  | piEta S q₀ q₁ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      intro Δ p
      exact .piEta (S ∪ supp Δ) (ih₀ p) (ih₁ p)
        (fun x hx => ih₂ x (notMem_union_left hx)
          (.snoc p h (notMem_union_right hx) (ih₃ p)))
        (ih₃ p)

/-- Agda: `▷⨟Jg` (MLTT/Weakening.agda). -/
theorem wkSnocDeriv {Δ Γ : Cx} {A : Ty0} {x : Atom} {l : Lvl} {J : Jg}
    (q : (Γ ⨟ x ∶ A ⦂ l) ⊢ J) (p : Δ ▷ Γ) (q' : x # Δ) : (Δ ⨟ x ∶ A ⦂ l) ⊢ J := by
  obtain ⟨_, hA, _⟩ := snocOkInv (derivOk q)
  exact wkDeriv (.snoc p hA q' (wkDeriv p hA)) q

/-! ## Admissible rule for context weakening -/

/-- Agda: `▷⨟⁻` (MLTT/Weakening.agda). -/
theorem wkSnoc {l : Lvl} {Δ Γ : Cx} {A : Ty0} {x : Atom} (p : Δ ▷ Γ) (q : Γ ⊢ A ⦂ l)
    (q' : x # Δ) : (Δ ⨟ x ∶ A ⦂ l) ▷ (Γ ⨟ x ∶ A ⦂ l) :=
  .snoc p q q' (wkDeriv p q)

end MLTT

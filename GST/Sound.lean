import GST.TermSemantics

/-!
# Soundness of conversion for the semantics of terms

Port of `agda-code/agda/GST/Sound.agda`.

Convertible terms have the same interpretation.  Agda needs the helper `sound'`,
which carries two equations between types and a `subst`, to make the recursion
structural.  Here the three arguments share one type index and dependent pattern
matching does the same work, so `sound` recurses directly on the conversion
derivation and inverts the two typing derivations with `cases`; the two places where
Agda's `⇒inj ∘ svTy` is genuinely needed (the congruence rule for application, and
the β-rule for `natrec` at a successor) are the `cases` on `arrow_inj (svTy …)`.
-/

namespace GST

open WSLN

/-- Agda: `sound` (GST/Sound.agda), with the conversion derivation first so that
matching on it refines the two subject terms before the typing derivations are
inspected; `sound` below restores Agda's argument order. -/
theorem soundAux : {S : Fset} → {Γ : Cx S} → {A : Ty} → {a a' : Tm0} →
    (q : Γ ⊢ a ＝ a' ∶ A) → (r : Γ ⊢ a ∶ A) → (r' : Γ ⊢ a' ∶ A) → {S' : Fset} →
    {Γ' : Cx S'} → (𝓼 : Psh.El (𝓔 Γ) Γ') → (𝓓 A).obj Γ' ∋ sem₀ r 𝓼 ~ sem₀ r' 𝓼
  | _, _, _, _, _, .refl _, r, r', _, _, 𝓼 => irrelSem r r' rfl 𝓼
  | _, _, A, _, _, .symm q, r, r', _, Γ', 𝓼 => ((𝓓 A).obj Γ').symm' (soundAux q r' r 𝓼)
  | _, _, A, _, _, .trans q₀ q₁, r, r', _, Γ', 𝓼 =>
      ((𝓓 A).obj Γ').trans' (soundAux q₀ r (convTy₂ q₀) 𝓼) (soundAux q₁ (convTy₂ q₀) r' 𝓼)
  | _, _, _, _, _, .lam (b := b₁) (b' := b₂) (x := x) (h := hx) q₀ hb, r, r',
      _, _, 𝓼 =>
      match r, r' with
      | .lam (B := B) (x := x₁) (h := hx₁) r₁ hb₁,
        .lam (x := x₂) (h := hx₂) r₂ hb₂ => fun z =>
          let r₁' := rnDerivBody x₁ x hx₁ hx b₁ r₁ hb₁ (Fset.notMem_union_left hb)
          let r₂' := rnDerivBody x₂ x hx₂ hx b₂ r₂ hb₂ (Fset.notMem_union_right hb)
          ((𝓓 B).obj _).trans'
            (rnSemBody hx₁ hx b₁ r₁ r₁' hb₁ (Fset.notMem_union_left hb)
              (((𝓔 _).act z.1).map 𝓼) z.2)
            (((𝓓 B).obj _).trans'
              (soundAux q₀ r₁' r₂' (((𝓔 _).act z.1).map 𝓼, z.2))
              (((𝓓 B).obj _).symm'
                (rnSemBody hx₂ hx b₂ r₂ r₂' hb₂ (Fset.notMem_union_right hb)
                  (((𝓔 _).act z.1).map 𝓼) z.2)))
  | _, _, _, _, _, .app q₀ q₁, r, r', _, _, 𝓼 => by
      match r, r' with
      | .app r₀ r₁, .app r₀' r₁' =>
        cases (arrow_inj (svTy r₀ (convTy₁ q₀))).1
        cases (arrow_inj (svTy r₀' (convTy₂ q₀))).1
        exact evResp (soundAux q₀ r₀ r₀' 𝓼) (soundAux q₁ r₁ r₁' 𝓼)
  | _, _, _, _, _, .succ q, r, r', _, _, 𝓼 =>
      match r, r' with
      | .succ r, .succ r' => congrArg (fun t => 𝐬𝐮𝐜𝐜 t) (soundAux q r r' 𝓼)
  | _, _, _, _, _, .nrec q₀ q₁ q₂, r, r', _, _, 𝓼 =>
      match r, r' with
      | .nrec r₀ r₁ r₂, .nrec r₀' r₁' r₂' =>
          nrecSem₂' (sem₀ r₂ 𝓼).pf (sem₀ r₂' 𝓼).pf (soundAux q₀ r₀ r₀' 𝓼)
            (soundAux q₁ r₁ r₁' 𝓼) (soundAux q₂ r₂ r₂' 𝓼)
  | _, Γ, B, _, _, .betaLam (b := b) (x := x) (h := hx) q₀ q₁ hb, r, r',
      _, Γ', 𝓼 =>
      match r with
      | .app (A := A) (.lam (x := x₀) (h := hx₀) r₀ hb₀) r₁ =>
          ((𝓓 B).obj Γ').trans'
            (((𝓓 B).obj Γ').trans'
              (((𝓓 B).obj Γ').trans'
                ((sem r₀).hom.resp
                  (show (𝓔 (Γ ⨟ x₀ ∶ A ∣ hx₀)).obj Γ' ∋
                      (((𝓔 Γ).act (RnHom.id Γ')).map 𝓼, sem₀ r₁ 𝓼) ~
                        (𝓼, sem₀ r₁ 𝓼) from
                    ⟨(𝓔 Γ).unit Γ' 𝓼, ((𝓓 A).obj Γ').rfl' (sem₀ r₁ 𝓼)⟩))
                (rnSemBody hx₀ hx b r₀ q₀ hb₀ hb 𝓼 (sem₀ r₁ 𝓼)))
              ((sem q₀).hom.resp
                (show (𝓔 (Γ ⨟ x ∶ A ∣ hx)).obj Γ' ∋
                    (𝓼, sem₀ r₁ 𝓼) ~ (𝓼, sem₀ q₁ 𝓼) from
                  ⟨((𝓔 Γ).obj Γ').rfl' 𝓼, irrelSem r₁ q₁ rfl 𝓼⟩)))
            (concSem b x hx q₀ q₁ r' hb 𝓼)
  | _, _, _, _, _, .betaZero _ _, r, r', _, _, 𝓼 =>
      match r with
      | .nrec r₀ _ .zero => irrelSem r₀ r' rfl 𝓼
  | _, _, _, _, _, .betaSucc _ _ _, r, r', _, _, 𝓼 => by
      match r, r' with
      | .nrec r₀ r₁ (.succ r₂), .app (.app r₀' r₁') (.nrec r₂' r₃' r₄') =>
        have h := arrow_inj (svTy r₀' r₃')
        cases h.1
        cases (arrow_inj h.2).2
        exact evResp
          (evResp (irrelSem r₁ r₀' rfl 𝓼) (irrelSem r₂ r₁' rfl 𝓼))
          (nrecSem₂' (sem₀ r₂ 𝓼).pf (sem₀ r₄' 𝓼).pf
            (irrelSem r₀ r₂' rfl 𝓼) (irrelSem r₁ r₃' rfl 𝓼) (irrelSem r₂ r₄' rfl 𝓼))
  | _, Γ, A₁ ⇒ B, _, _, .eta (b := b) (x := x') _ hb, r, r', _, _, 𝓼 =>
      match r' with
      | .lam (x := x) (h := hΓ) r₀ hb₀ => fun z =>
          let r₀' : (Γ ⨟ x ∶ A₁ ∣ hΓ) ⊢ b ∙ 𝐯x ∶ B := .app (wkDeriv hΓ r) (.var .new)
          have e₃ : (b ∙ 𝐯x : Tm0) = (x' ． b ∙ 𝐯x')[x] := by
            rw [conc_atom, ← conc_trm, concAbs x' (b ∙ 𝐯x') (Trm.atom x)]
            show _ = ((x' ≔ (𝐯x : Tm0)) * b) ∙ ((x' ≔ (𝐯x : Tm0)) * (𝐯x' : Tm0))
            rw [ssbFresh x' (𝐯x) b hb]
            show _ = b ∙ ((x' ≔ (𝐯x : Tm0)) * (Trm.atom x' : Tm0))
            rw [Sb.single_def x' (𝐯x : Tm0), updateEq]
          ((𝓓 B).obj _).trans'
            (((𝓓 B).obj _).symm'
              (((𝓓 B).obj _).trans' ((sem r).ntl z.1 𝓼 (RnHom.id _, z.2))
                ((sem₀ r 𝓼).hom.resp
                  (show (yon _ ×^ 𝓓 A₁).obj _ ∋
                      (z.1 ∘ᵣ RnHom.id _, z.2) ~ (z.1, z.2) from
                    ⟨fun _ _ => rfl, ((𝓓 A₁).obj _).rfl' z.2⟩))))
            (((𝓓 B).obj _).trans'
              (((𝓓 B).obj _).symm'
                (evResp (wkSem hΓ r (wkDeriv hΓ r) (((𝓔 Γ).act z.1).map 𝓼) z.2)
                  (((𝓓 A₁).obj _).rfl' z.2)))
              (irrelSem r₀' r₀ e₃ (((𝓔 Γ).act z.1).map 𝓼, z.2)))

/-- Agda: `sound` (GST/Sound.agda). -/
theorem sound {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} (r : Γ ⊢ a ∶ A)
    (r' : Γ ⊢ a' ∶ A) (q : Γ ⊢ a ＝ a' ∶ A) {S' : Fset} {Γ' : Cx S'}
    (𝓼 : Psh.El (𝓔 Γ) Γ') : (𝓓 A).obj Γ' ∋ sem₀ r 𝓼 ~ sem₀ r' 𝓼 := soundAux q r r' 𝓼

end GST

import GST.TypeSystem

/-!
# Provable judgements are well-scoped

Port of `agda-code/agda/GST/WellScoped.agda`.

The two mutually recursive Agda functions `supp＝₁`/`supp＝₂` are one Lean induction
proving their conjunction (`supp_conv`), with the Agda statements recovered as its two
projections; likewise the auxiliary `supp⊢¹`/`supp＝₁¹`/`supp＝₂¹`, whose only role is
to feed the induction hypothesis for a λ-body through `[]supp`, are inlined.
-/

namespace GST

open WSLN

/-! ## Provable typings are well-scoped -/

/-- Support of one λ-body: a name occurring in the body occurs in the context, since the
concreting atom is fresh for the body. -/
theorem supp_body {S : Fset} {x y : Atom} {b : Tm 1} (hb : x # b)
    (h : supp (b[x]) ⊆ S ∪ ｛ x ｝) (hy : y ∈ supp b) : y ∈ S :=
  Fset.mem_left_of_notMem_right (h (conc_supp b (Trm.atom x) hy))
    (.single fun e => Fset.not_mem_of_notMem hb (e ▸ hy))

theorem supp_deriv {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} (q : Γ ⊢ a ∶ A) :
    supp a ⊆ dom Γ := by
  induction q with
  | var q => intro y hy; cases hy; exact isIn_dom q
  | @lam _ _ _ _ b _ _ _ q₁ ih =>
      intro y hy
      rw [supp_lam] at hy
      cases hy with
      | unionL hy => exact supp_body q₁ ih hy
      | unionR hy => cases hy
  | app _ _ ih₀ ih₁ =>
      intro y hy
      rw [supp_app] at hy
      cases hy with
      | unionL hy => exact ih₀ hy
      | unionR hy => cases hy with
        | unionL hy => exact ih₁ hy
        | unionR hy => cases hy
  | zero => intro y hy; cases hy
  | succ _ ih =>
      intro y hy
      rw [supp_succ] at hy
      cases hy with
      | unionL hy => exact ih hy
      | unionR hy => cases hy
  | nrec _ _ _ ih₀ ih₁ ih₂ =>
      intro y hy
      rw [supp_nrec] at hy
      cases hy with
      | unionL hy => exact ih₀ hy
      | unionR hy => cases hy with
        | unionL hy => exact ih₁ hy
        | unionR hy => cases hy with
          | unionL hy => exact ih₂ hy
          | unionR hy => cases hy

/-! ## Provable conversions are well-scoped -/

/-- Provable conversions have well-scoped subjects, both sides proved as one induction. -/
theorem supp_conv {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} (q : Γ ⊢ a ＝ a' ∶ A) :
    supp a ⊆ dom Γ ∧ supp a' ⊆ dom Γ := by
  induction q with
  | refl q => exact ⟨supp_deriv q, supp_deriv q⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₀ ih₁ => exact ⟨ih₀.1, ih₁.2⟩
  | @lam _ _ _ _ b b' _ _ _ q₁ ih =>
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [supp_lam] at hy
        cases hy with
        | unionL hy => exact supp_body (Fset.notMem_union_left q₁) ih.1 hy
        | unionR hy => cases hy
      · intro y hy
        rw [supp_lam] at hy
        cases hy with
        | unionL hy =>
            exact supp_body (Fset.notMem_union_right q₁) ih.2 hy
        | unionR hy => cases hy
  | app _ _ ih₀ ih₁ =>
      constructor <;> · intro y hy
                        rw [supp_app] at hy
                        cases hy with
                        | unionL hy => first | exact ih₀.1 hy | exact ih₀.2 hy
                        | unionR hy => cases hy with
                          | unionL hy => first | exact ih₁.1 hy | exact ih₁.2 hy
                          | unionR hy => cases hy
  | succ _ ih =>
      constructor <;> · intro y hy
                        rw [supp_succ] at hy
                        cases hy with
                        | unionL hy => first | exact ih.1 hy | exact ih.2 hy
                        | unionR hy => cases hy
  | nrec _ _ _ ih₀ ih₁ ih₂ =>
      constructor <;> · intro y hy
                        rw [supp_nrec] at hy
                        cases hy with
                        | unionL hy => first | exact ih₀.1 hy | exact ih₀.2 hy
                        | unionR hy => cases hy with
                          | unionL hy => first | exact ih₁.1 hy | exact ih₁.2 hy
                          | unionR hy => cases hy with
                            | unionL hy => first | exact ih₂.1 hy | exact ih₂.2 hy
                            | unionR hy => cases hy
  | @betaLam _ _ _ _ a b _ _ q₀ q₁ q₂ =>
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [supp_app, supp_lam] at hy
        cases hy with
        | unionL hy =>
            cases hy with
            | unionL hy => exact supp_body q₂ (supp_deriv q₀) hy
            | unionR hy => cases hy
        | unionR hy =>
            cases hy with
            | unionL hy => exact supp_deriv q₁ hy
            | unionR hy => cases hy
      · intro y hy
        cases supp_conc b a hy with
        | unionL hy => exact supp_body q₂ (supp_deriv q₀) hy
        | unionR hy => exact supp_deriv q₁ hy
  | betaZero q₀ q₁ =>
      refine ⟨?_, supp_deriv q₀⟩
      intro y hy
      rw [supp_nrec] at hy
      cases hy with
      | unionL hy => exact supp_deriv q₀ hy
      | unionR hy => cases hy with
        | unionL hy => exact supp_deriv q₁ hy
        | unionR hy => cases hy with
          | unionL hy => cases hy
          | unionR hy => cases hy
  | betaSucc q₀ q₁ q₂ =>
      have h₀ := supp_deriv q₀
      have h₁ := supp_deriv q₁
      have h₂ := supp_deriv q₂
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [supp_nrec, supp_succ] at hy
        cases hy with
        | unionL hy => exact h₀ hy
        | unionR hy => cases hy with
          | unionL hy => exact h₁ hy
          | unionR hy => cases hy with
            | unionL hy =>
                cases hy with
                | unionL hy => exact h₂ hy
                | unionR hy => cases hy
            | unionR hy => cases hy
      · intro y hy
        rw [supp_app, supp_app, supp_nrec] at hy
        cases hy with
        | unionL hy =>
            cases hy with
            | unionL hy => exact h₁ hy
            | unionR hy => cases hy with
              | unionL hy => exact h₂ hy
              | unionR hy => cases hy
        | unionR hy =>
            cases hy with
            | unionL hy =>
                cases hy with
                | unionL hy => exact h₀ hy
                | unionR hy => cases hy with
                  | unionL hy => exact h₁ hy
                  | unionR hy => cases hy with
                    | unionL hy => exact h₂ hy
                    | unionR hy => cases hy
            | unionR hy => cases hy
  | @eta _ _ _ _ b x q₀ q₁ =>
      have h₀ := supp_deriv q₀
      refine ⟨h₀, ?_⟩
      intro y hy
      rw [supp_lam, abs_app] at hy
      cases hy with
      | unionL hy =>
          rw [supp_app] at hy
          cases hy with
          | unionL hy => exact h₀ (suppAbs x b hy)
          | unionR hy =>
              cases hy with
              | unionL hy => rw [vr, Trm.abs, cls_atom_eq] at hy; cases hy
              | unionR hy => cases hy
      | unionR hy => cases hy

theorem supp_conv₁ {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0}
    (q : Γ ⊢ a ＝ a' ∶ A) : supp a ⊆ dom Γ := (supp_conv q).1

theorem supp_conv₂ {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0}
    (q : Γ ⊢ a ＝ a' ∶ A) : supp a' ⊆ dom Γ := (supp_conv q).2

/-! ## Freshness property of provable judgements -/

theorem fresh_deriv {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} {x : Atom}
    (q : Γ ⊢ a ∶ A) (h : x ∉ᶠ S) : x # a := Fset.subset_notMem (supp_deriv q) h

theorem fresh_conv₁ {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} {x : Atom}
    (q : Γ ⊢ a ＝ a' ∶ A) (h : x ∉ᶠ S) : x # a := Fset.subset_notMem (supp_conv₁ q) h

theorem fresh_conv₂ {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} {x : Atom}
    (q : Γ ⊢ a ＝ a' ∶ A) (h : x ∉ᶠ S) : x # a' := Fset.subset_notMem (supp_conv₂ q) h

end GST

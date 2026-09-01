import MLTT.Cofinite

/-!
# Well-formed contexts

Port of `agda-code/agda/MLTT/Ok.agda`.

Lean's `induction` tactic does not support mutually inductive types directly, so
inductions over `Deriv` go through the joint recursor:

```
induction h using Deriv.rec (motive_1 := fun _ _ => True) with
  | nil => trivial            -- the `Ok.nil` case
  | snoc .. => trivial        -- the `Ok.snoc` case
  | conv q₀ q₁ ih₀ ih₁ => …   -- the 30 `Deriv` cases
```

For genuinely joint inductions (e.g. `okSupp`/`derivSupp` in `MLTT/WellScoped.lean`)
supply both motives.

`derivOk` needs no explicit branches: every one of the thirty `Deriv` constructors is
closed by its direct `Ok` premise or by an induction hypothesis, and the two `Ok`
constructors are `True` under `motive_1`.
-/

namespace MLTT

open WSLN

/-! ## Provable judgements have well-formed contexts -/

/-- Agda: `⊢ok` (MLTT/Ok.agda). -/
theorem derivOk {Γ : Cx} {J : Jg} (h : Γ ⊢ J) : Ok Γ := by
  induction h using Deriv.rec (motive_1 := fun _ _ => True) <;>
    first | trivial | assumption

/-- Agda: `ok＝` (MLTT/Ok.agda). -/
theorem okEq₁ {Γ Γ' : Cx} (h : ⊢ Γ ＝ Γ') : Ok Γ := by
  induction h with
  | nil => exact .nil
  | snoc _ _ q₂ h₀ _ ih => exact .snoc h₀ (Fset.notMem_union_left q₂) ih

/-- Agda: `＝ok` (MLTT/Ok.agda). -/
theorem okEq₂ {Γ Γ' : Cx} (h : ⊢ Γ ＝ Γ') : Ok Γ' := by
  induction h with
  | nil => exact .nil
  | snoc _ _ q₂ _ h₁ ih => exact .snoc h₁ (Fset.notMem_union_right q₂) ih

/-- Agda: `dom▷` (MLTT/Ok.agda). -/
theorem domWk {Δ Γ : Cx} (h : Δ ▷ Γ) : dom Γ ⊆ dom Δ := by
  induction h with
  | nil => exact fun _ p => p
  | proj _ _ _ ih => exact fun _ p => .unionL (ih p)
  | snoc _ _ _ _ ih =>
      exact Fset.union_subset (fun _ p => .unionL (ih p)) (fun _ p => .unionR p)

/-- Agda: `▷Ok` (MLTT/Ok.agda). -/
theorem wkOk {Δ Γ : Cx} (h : Δ ▷ Γ) : Ok Γ := by
  induction h with
  | nil => exact .nil
  | proj _ _ _ ih => exact ih
  | @snoc _ _ _ _ _ q₀ q₁ q₂ _ ih =>
      exact .snoc q₁ (Fset.subset_notMem (domWk q₀) q₂) ih

/-- Agda: `Ok▷` (MLTT/Ok.agda). -/
theorem okWk {Δ Γ : Cx} (h : Δ ▷ Γ) : Ok Δ := by
  induction h with
  | nil => exact .nil
  | proj _ q₁ q₂ ih => exact .snoc q₁ q₂ ih
  | snoc _ _ q₂ hh ih => exact .snoc hh q₂ ih

/-- Agda: `sbOk` (MLTT/Ok.agda). -/
theorem sbOk {Γ' Γ : Cx} {σ : Sb sig} (h : Γ' ⊢ˢ σ ∶ Γ) : Ok Γ := by
  induction h with
  | nil _ => exact .nil
  | snoc _ q₁ _ q₃ ih => exact .snoc q₁ q₃ ih

/-- Agda: `okSb` (MLTT/Ok.agda). -/
theorem okSb {Γ' Γ : Cx} {σ : Sb sig} (h : Γ' ⊢ˢ σ ∶ Γ) : Ok Γ' := by
  induction h with
  | nil q => exact q
  | snoc _ _ _ _ ih => exact ih

/-- Agda: `sb＝Ok` (MLTT/Ok.agda). -/
theorem sbEqOk {Γ' Γ : Cx} {σ σ' : Sb sig} (h : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) : Ok Γ := by
  induction h with
  | nil _ => exact .nil
  | snoc _ q₁ _ q₃ ih => exact .snoc q₁ q₃ ih

/-- Agda: `okSb＝` (MLTT/Ok.agda). -/
theorem okSbEq {Γ' Γ : Cx} {σ σ' : Sb sig} (h : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) : Ok Γ' := by
  induction h with
  | nil q => exact q
  | snoc _ _ _ _ ih => exact ih

/-! ## Context inversion -/

/-- Agda: `[]⁻¹` (MLTT/Ok.agda). -/
theorem snocOkInv {l : Lvl} {Γ : Cx} {A : Ty0} {x : Atom} (h : Ok (Γ ⨟ x ∶ A ⦂ l)) :
    (x # Γ) ∧ (Γ ⊢ A ⦂ l) ∧ Ok Γ := by
  cases h with
  | snoc q₀ q₁ hh => exact ⟨q₁, q₀, hh⟩

/-! ## Context formation without the helper hypothesis -/

/-- Agda: `ok⨟⁻` (MLTT/Ok.agda). -/
theorem okSnoc {l : Lvl} {Γ : Cx} {A : Ty0} {x : Atom} (q : Γ ⊢ A ⦂ l) (q' : x # Γ) :
    Ok (Γ ⨟ x ∶ A ⦂ l) := .snoc q q' (derivOk q)

end MLTT

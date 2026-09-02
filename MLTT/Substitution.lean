import MLTT.Weakening

/-!
# Substitution

Port of `agda-code/agda/MLTT/Substitution.agda`.

`sbDeriv` and `eqSbTm` are two independent exhaustive inductions over the thirty
constructors of `Deriv`, generalised over the target context and the substitution(s).
Following `MLTT/Weakening.lean` the generalised variables are `revert`ed and the
induction goes through the joint `Ok`/`Deriv` recursor with
`motive_1 := fun _ _ => True`.

Agda's `＝sbTm` only has clauses for the *typing* constructors, because its statement
fixes the judgement to be of the form `a ∶ A ⦂ l`.  Lean's `Deriv.rec` insists on all
thirty cases, so the induction is carried out for the auxiliary predicate
`eqSbTmGoal`, which is `True` on conversion judgements; `eqSbTm` itself has exactly
the Agda statement.

Agda's `subst`/`subst₂`/`subst₃` transports on judgements are shared, so the
`castIsTy`/`castTyEq`/`castTm`/`castEq` helpers live in `MLTT/Cofinite.lean`, and the
definitional equations for the action of a substitution on the pattern constructors of
`MLTT/Syntax.lean` (which Agda gets for free from its pattern synonyms) live there;
only `sbU`, `sbNat` and `sbZero`, which no other module needs, stay `private` here.
-/

namespace MLTT

open WSLN
open Fset

/-! ## Plumbing with no Agda counterpart -/

/-- Agda writes `symm (:=Neq {f = σ} x y λ{refl → ∉→¬∈ x#Γ r})` inline. -/
private theorem updateNeqDom {σ : Sb sig} {Γ : Cx} {x : Atom} {u : Tm0} (hx : x # Γ)
    {y : Atom} (hy : y ∈ dom Γ) : σ y = (σ ∘/ x ≔ u) y := by
  refine (Sb.update_neq σ u ?_).symm
  intro ee
  subst ee
  exact Fset.not_mem_of_notMem hx hy

/-! ### Definitional equations for the action on the pattern constructors -/

private theorem sbU {n : Nat} (σ : Sb sig) (l : Lvl) : σ * (𝐔 l : Ty n) = 𝐔 l := rfl

private theorem sbNat {n : Nat} (σ : Sb sig) : σ * (𝐍𝐚𝐭 : Ty n) = 𝐍𝐚𝐭 := rfl

private theorem sbZero {n : Nat} (σ : Sb sig) : σ * (𝐳𝐞𝐫𝐨 : Tm n) = 𝐳𝐞𝐫𝐨 := rfl

/-! ## Weakening substitutions -/

theorem wkSb {l : Lvl} {Γ Γ' : Cx} {σ : Sb sig} {A : Ty0} (x : Atom)
    (q : Γ' ⊢ A ⦂ l) (q' : Γ' ⊢ˢ σ ∶ Γ) (q'' : x # Γ') :
    (Γ' ⨟ x ∶ A ⦂ l) ⊢ˢ σ ∶ Γ := by
  induction q' with
  | nil hΓ' => exact .nil (.snoc q q'' hΓ')
  | snoc _ q₁ q₂ q₃ ih => exact .snoc (ih q q'') q₁ (wkDeriv (wkProj q q'') q₂) q₃

theorem wkEqSb {l : Lvl} {Γ Γ' : Cx} {σ σ' : Sb sig} {A : Ty0} (x : Atom)
    (q : Γ' ⊢ A ⦂ l) (q' : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) (q'' : x # Γ') :
    (Γ' ⨟ x ∶ A ⦂ l) ⊢ˢ σ ＝ σ' ∶ Γ := by
  induction q' with
  | nil hΓ' => exact .nil (.snoc q q'' hΓ')
  | snoc _ q₁ q₂ q₃ ih => exact .snoc (ih q q'') q₁ (wkDeriv (wkProj q q'') q₂) q₃

/-! ## Identity substitution is well-typed -/

theorem idSbTyping {Γ : Cx} (p : Ok Γ) : Γ ⊢ˢ Sb.id ∶ Γ := by
  revert p
  induction Γ with
  | nil => intro _; exact .nil .nil
  | snoc Γ x A l ih =>
      intro p
      cases p with
      | snoc q₀ q₁ hh =>
          refine .snoc (wkSb x q₀ (ih hh) q₁) q₀ ?_ q₁
          rw [sbUnit]
          exact .var (okSnoc q₀ q₁) .new

/-! ## Extensionality properties of well-typed substitutions -/

theorem sbExt {σ σ' : Sb sig} {Γ Γ' : Cx} (p : Γ' ⊢ˢ σ ∶ Γ)
    (e : ∀ x, x ∈ dom Γ → σ x = σ' x) : Γ' ⊢ˢ σ' ∶ Γ := by
  revert e
  induction p with
  | nil q => intro _; exact .nil q
  | @snoc l Γ₀ Δ₀ σ₀ A x _ q₁ q₂ q₃ ih =>
      intro e
      have eA : σ₀ * A = σ' * A :=
        sbRespSupp σ₀ σ' A fun y hy =>
          e y (.unionL ((Fset.union_subset_iff.mp (derivSupp q₁)).1 hy))
      refine .snoc (ih fun y r => e y (.unionL r)) q₁ ?_ q₃
      exact castTm (e x (.unionR .single)) eA q₂

theorem sbEqExt {σ' τ' σ τ : Sb sig} {Γ Γ' : Cx} (p : Γ' ⊢ˢ σ ＝ τ ∶ Γ)
    (e : ∀ x, x ∈ dom Γ → σ x = σ' x) (e' : ∀ x, x ∈ dom Γ → τ x = τ' x) :
    Γ' ⊢ˢ σ' ＝ τ' ∶ Γ := by
  revert e e'
  induction p with
  | nil q => intro _ _; exact .nil q
  | @snoc l Γ₀ Δ₀ σ₀ τ₀ A x _ q₁ q₂ q₃ ih =>
      intro e e'
      have eA : σ₀ * A = σ' * A :=
        sbRespSupp σ₀ σ' A fun y hy =>
          e y (.unionL ((Fset.union_subset_iff.mp (derivSupp q₁)).1 hy))
      refine .snoc (ih (fun y r => e y (.unionL r)) (fun y r => e' y (.unionL r)))
        q₁ ?_ q₃
      exact castEq (e x (.unionR .single)) (e' x (.unionR .single)) eA q₂

/-! ## Lifting substitutions -/

theorem liftSb {l : Lvl} {σ : Sb sig} {Γ Γ' : Cx} {A : Ty0} {x x' : Atom}
    (p : Γ' ⊢ˢ σ ∶ Γ) (q : Γ ⊢ A ⦂ l) (hx : x # Γ) (hx' : x' # Γ')
    (h : Γ' ⊢ σ * A ⦂ l) :
    (Γ' ⨟ x' ∶ σ * A ⦂ l) ⊢ˢ (σ ∘/ x ≔ 𝐯x') ∶ (Γ ⨟ x ∶ A ⦂ l) := by
  have p' : Γ' ⊢ˢ (σ ∘/ x ≔ (𝐯x' : Tm0)) ∶ Γ :=
    sbExt p fun y r => updateNeqDom hx r
  refine .snoc (wkSb x' h p' hx') q ?_ hx
  have hxA : x # A := notMem_union_left (derivFresh q hx)
  rw [updateFresh σ x (𝐯x') A hxA, Sb.update_eq]
  exact .var (okSnoc h hx') .new

theorem liftSb₂ {l l' : Lvl} {σ : Sb sig} {Γ Γ' : Cx} {A A' B B' : Ty0}
    {x y x' y' : Atom} (q₀ : Γ' ⊢ˢ σ ∶ Γ) (q₁ : Γ ⊢ A ⦂ l)
    (q₂ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B ⦂ l') (q₃ : x' # Γ') (q₄ : y # (Γ, x))
    (q₅ : y' # (Γ', x')) (e : σ * A = A') (e' : (σ ∘/ x ≔ 𝐯x') * B = B')
    (h : Γ' ⊢ A' ⦂ l) (h' : (Γ' ⨟ x' ∶ A' ⦂ l) ⊢ B' ⦂ l') :
    (Γ' ⨟ x' ∶ A' ⦂ l ⨟ y' ∶ B' ⦂ l') ⊢ˢ ((σ ∘/ x ≔ 𝐯x') ∘/ y ≔ 𝐯y') ∶
      (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') := by
  subst e; subst e'
  exact liftSb (liftSb q₀ q₁ (snocOkInv (derivOk q₂)).1 q₃ h) q₂ q₄ q₅ h'

/-! ## Types of variables under substitution -/

theorem sbVar {l : Lvl} {σ : Sb sig} {Γ Γ' : Cx} {x : Atom} {A : Ty0}
    (p : Γ' ⊢ˢ σ ∶ Γ) (q : (x, A, l) isIn Γ) : Γ' ⊢ σ x ∶ σ * A ⦂ l := by
  revert q
  induction p with
  | nil _ => intro q; cases q
  | snoc _ _ q₂ _ ih =>
      intro q
      cases q with
      | new => exact q₂
      | old q' => exact ih q'

theorem sbVarEq {l : Lvl} {σ σ' : Sb sig} {Γ Γ' : Cx} {x : Atom} {A : Ty0}
    (p : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) (q : (x, A, l) isIn Γ) :
    Γ' ⊢ σ x ＝ σ' x ∶ σ * A ⦂ l := by
  revert q
  induction p with
  | nil _ => intro q; cases q
  | snoc _ _ q₂ _ ih =>
      intro q
      cases q with
      | new => exact q₂
      | old q' => exact ih q'

theorem sbDom {σ : Sb sig} {Γ Γ' : Cx} {x : Atom} (p : Γ' ⊢ˢ σ ∶ Γ)
    (q : x ∈ dom Γ) : supp (σ x) ⊆ dom Γ' := by
  obtain ⟨A, l, q'⟩ := dom_isIn q
  exact (Fset.union_subset_iff.mp (derivSupp (sbVar p q'))).1

/-! ## Substitution preserves provable judgements -/

set_option maxHeartbeats 400000 in
theorem sbDeriv {σ : Sb sig} {Δ Γ : Cx} {J : Jg} (p : Δ ⊢ˢ σ ∶ Γ) (q : Γ ⊢ J) :
    Δ ⊢ σ * J := by
  revert σ Δ
  induction q using Deriv.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc _ _ _ _ _ => trivial
  | conv _ _ ih₀ ih₁ =>
      intro σ Δ p
      exact .conv (ih₀ p) (ih₁ p)
  | var _ q₁ _ =>
      intro σ Δ p
      exact castTm (sbAtom σ _).symm rfl (sbVar p q₁)
  | univ _ _ =>
      intro σ Δ p
      exact .univ (okSb p)
  | @pi Γ l l' A B S q₀ q₁ ih₀ ih₁ =>
      intro σ Δ p
      refine .pi (S ∪ supp (Δ, B)) (ih₀ p) (fun x hx => ?_)
      have hxS : x # S := notMem_union_left hx
      have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
      have hxB : x # B := notMem_union_right (notMem_union_right hx)
      have hxΓ : x # Γ := (snocOkInv (derivOk (q₁ x hxS))).1
      exact castIsTy
        (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
          sbUpdate_conc σ x (𝐯x) B hxB)
        (ih₁ x hxS (liftSb p q₀ hxΓ hxΔ (ih₀ p)))
  | @lam Γ l l' A B b S _ h₀ h₁ ih₀ ih₁ ih₂ =>
      intro σ Δ p
      refine .lam (S ∪ supp (Δ, B, b)) (fun x hx => ?_) (ih₁ p) (fun x hx => ?_)
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        have hxb : x # b :=
          notMem_union_right (notMem_union_right (notMem_union_right hx))
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        exact castTm
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (b[x]) = (σ * b)[x] from
            sbUpdate_conc σ x (𝐯x) b hxb)
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (ih₀ x hxS (liftSb p h₀ hxΓ hxΔ (ih₁ p)))
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        exact castIsTy
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (ih₂ x hxS (liftSb p h₀ hxΓ hxΔ (ih₁ p)))
  | @app Γ l l' A B a b S _ _ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      intro σ Δ p
      refine castTm rfl (sb_conc σ B a).symm ?_
      refine .app (S ∪ supp (Δ, B)) (ih₀ p) (ih₁ p) (fun x hx => ?_) (ih₃ p)
      have hxS : x # S := notMem_union_left hx
      have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
      have hxB : x # B := notMem_union_right (notMem_union_right hx)
      have hxΓ : x # Γ := (snocOkInv (derivOk (q₂ x hxS))).1
      exact castIsTy
        (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
          sbUpdate_conc σ x (𝐯x) B hxB)
        (ih₂ x hxS (liftSb p h hxΓ hxΔ (ih₃ p)))
  | idF _ _ _ ih₀ ih₁ ih₂ =>
      intro σ Δ p
      exact .idF (ih₀ p) (ih₁ p) (ih₂ p)
  | reflI _ _ ih₀ ih₁ =>
      intro σ Δ p
      exact .reflI (ih₀ p) (ih₁ p)
  | @j Γ l l' A C a b c ee S q₀ q₁ q₂ q₃ q₄ h₀ h₁ ih₀ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
      intro σ Δ p
      refine castTm rfl (sb_conc₂ σ C b ee).symm ?_
      have key : ∀ x, x # S → x # Δ →
          ((σ ∘/ x ≔ (𝐯x : Tm0)) * (𝐈𝐝 A a (𝐯x) : Ty0) = 𝐈𝐝 (σ * A) (σ * a) (𝐯x)) ∧
          ((Δ ⨟ x ∶ σ * A ⦂ l) ⊢ 𝐈𝐝 (σ * A) (σ * a) (𝐯x) ⦂ l) := by
        intro x hxS hxΔ
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        have hfr := derivFresh q₁ hxΓ
        have hxa : x # a := notMem_union_left hfr
        have hxA : x # A := notMem_union_right hfr
        have eqI : (σ ∘/ x ≔ (𝐯x : Tm0)) * (𝐈𝐝 A a (𝐯x) : Ty0)
            = 𝐈𝐝 (σ * A) (σ * a) (𝐯x) := by
          rw [sbId, updateFresh σ x (𝐯x) A hxA, updateFresh σ x (𝐯x) a hxa,
            sbAtom, Sb.update_eq]
        exact ⟨eqI, castIsTy eqI (ih₆ x hxS (liftSb p h₀ hxΓ hxΔ (ih₅ p)))⟩
      refine .j (S ∪ supp (Δ, C)) ?_ (ih₁ p) (ih₂ p) ?_ (ih₄ p) (ih₅ p)
        (fun x hx => (key x (notMem_union_left hx)
          (notMem_union_left (notMem_union_right hx))).2)
      · intro x y hfr2
        obtain ⟨hy, hxx, hxy⟩ := Fresh₂.inv hfr2
        have hxS : x # S := notMem_union_left hxx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hxx)
        have hxC : x # C := notMem_union_right (notMem_union_right hxx)
        have hyS : y # S := notMem_union_left hy
        have hyΔ : y # Δ := notMem_union_left (notMem_union_right hy)
        have hyC : y # C := notMem_union_right (notMem_union_right hy)
        obtain ⟨eqI, hId⟩ := key x hxS hxΔ
        have hyΓ : y # Γ := (snocOkInv (derivOk (h₁ y hyS))).1
        have pl := liftSb₂ p h₀ (h₁ x hxS) hxΔ (NotMem.union hyΓ (fresh_symm hxy))
          (NotMem.union hyΔ (fresh_symm hxy)) rfl eqI (ih₅ p) hId
        exact castIsTy
          (show ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (C[x][y]) = (σ * C)[x][y]
            from sbUpdate_conc₂ σ x y (𝐯x) (𝐯y) C hxC
              (NotMem.union hyC (fresh_symm hxy)))
          (ih₀ x y (Fresh₂.intro hyS hxS hxy) pl)
      · exact castTm rfl
          (show σ * (C[a][𝐫𝐞𝐟𝐥 a]) = (σ * C)[σ * a][𝐫𝐞𝐟𝐥 (σ * a)] from
            sb_conc₂ σ C a (𝐫𝐞𝐟𝐥 a))
          (ih₃ p)
  | nat _ =>
      intro σ Δ p
      exact .nat (okSb p)
  | zero _ =>
      intro σ Δ p
      exact .zero (okSb p)
  | succ _ ih =>
      intro σ Δ p
      exact .succ (ih p)
  | @nrec Γ l C c₀ a cs S q₀ q₁ _ h ih₀ ih₁ ih₂ ih₃ =>
      intro σ Δ p
      refine castTm rfl (sb_conc σ C a).symm ?_
      have key : ∀ x, x # S → x # Δ → x # C →
          (x # Γ) ∧ ((Δ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) ⊢ (σ * C)[x] ⦂ l) := by
        intro x hxS hxΔ hxC
        have hxΓ : x # Γ := (snocOkInv (derivOk (h x hxS))).1
        exact ⟨hxΓ, castIsTy
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] from
            sbUpdate_conc σ x (𝐯x) C hxC)
          (ih₃ x hxS (liftSb p (Deriv.nat (derivOk q₀)) hxΓ hxΔ
            (Deriv.nat (okSb p))))⟩
      refine .nrec (S ∪ supp (Δ, C, cs)) ?_ ?_ (ih₂ p)
        (fun x hx => (key x (notMem_union_left hx)
          (notMem_union_left (notMem_union_right hx))
          (notMem_union_left (notMem_union_right (notMem_union_right hx)))).2)
      · exact castTm rfl
          (show σ * (C[(𝐳𝐞𝐫𝐨 : Tm0)]) = (σ * C)[(𝐳𝐞𝐫𝐨 : Tm0)] from sb_conc σ C 𝐳𝐞𝐫𝐨)
          (ih₀ p)
      · intro x y hfr2
        obtain ⟨hy, hxx, hxy⟩ := Fresh₂.inv hfr2
        have hxS : x # S := notMem_union_left hxx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hxx)
        have hxC : x # C :=
          notMem_union_left (notMem_union_right (notMem_union_right hxx))
        have hxcs : x # cs :=
          notMem_union_right (notMem_union_right (notMem_union_right hxx))
        have hyS : y # S := notMem_union_left hy
        have hyΔ : y # Δ := notMem_union_left (notMem_union_right hy)
        have hyC : y # C :=
          notMem_union_left (notMem_union_right (notMem_union_right hy))
        have hycs : y # cs :=
          notMem_union_right (notMem_union_right (notMem_union_right hy))
        obtain ⟨hxΓ, hC⟩ := key x hxS hxΔ hxC
        have hfrS : x # y # S := Fresh₂.intro hyS hxS hxy
        have hyΓx : y # (Γ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) :=
          (snocOkInv (derivOk (q₁ x y hfrS))).1
        have hyx : y ≠ x := (Fset.ne_of_notMem_single hxy).symm
        have eqC : ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) *
            (C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)]) = (σ * C)[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] := by
          rw [sb_conc, updateFresh (σ ∘/ x ≔ (𝐯x : Tm0)) y (𝐯y) C hyC,
            updateFresh σ x (𝐯x) C hxC, sbSucc, sbAtom,
            Sb.update_neq _ _ hyx, Sb.update_eq]
        have pl := liftSb₂ p (Deriv.nat (derivOk q₀)) (h x hxS) hxΔ hyΓx
          (NotMem.union hyΔ (fresh_symm hxy)) (sbNat σ)
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] from
            sbUpdate_conc σ x (𝐯x) C hxC)
          (Deriv.nat (okSb p)) hC
        exact castTm
          (show ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (cs[x][y])
            = (σ * cs)[x][y] from sbUpdate_conc₂ σ x y (𝐯x) (𝐯y) cs hxcs
              (NotMem.union hycs (fresh_symm hxy)))
          eqC (ih₁ x y hfrS pl)
  | refl _ ih =>
      intro σ Δ p
      exact .refl (ih p)
  | symm _ ih =>
      intro σ Δ p
      exact .symm (ih p)
  | trans _ _ ih₀ ih₁ =>
      intro σ Δ p
      exact .trans (ih₀ p) (ih₁ p)
  | eqConv _ _ ih₀ ih₁ =>
      intro σ Δ p
      exact .eqConv (ih₀ p) (ih₁ p)
  | @piCong Γ l l' A A' B B' S _ q₁ h ih₀ ih₁ ih₂ =>
      intro σ Δ p
      refine .piCong (S ∪ supp (Δ, B, B')) (ih₀ p) (fun x hx => ?_) (ih₂ p)
      have hxS : x # S := notMem_union_left hx
      have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
      have hxB : x # B :=
        notMem_union_left (notMem_union_right (notMem_union_right hx))
      have hxB' : x # B' :=
        notMem_union_right (notMem_union_right (notMem_union_right hx))
      have hxΓ : x # Γ := (snocOkInv (derivOk (q₁ x hxS))).1
      exact castTyEq
        (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
          sbUpdate_conc σ x (𝐯x) B hxB)
        (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B'[x]) = (σ * B')[x] from
          sbUpdate_conc σ x (𝐯x) B' hxB')
        (ih₁ x hxS (liftSb p h hxΓ hxΔ (ih₂ p)))
  | @lamCong Γ l l' A A' B b b' S _ q₁ h₀ h₁ ih₀ ih₁ ih₂ ih₃ =>
      intro σ Δ p
      refine .lamCong (S ∪ supp (Δ, B, b, b')) (ih₀ p) (fun x hx => ?_) (ih₂ p)
        (fun x hx => ?_)
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        have hxb : x # b :=
          notMem_union_left
            (notMem_union_right (notMem_union_right (notMem_union_right hx)))
        have hxb' : x # b' :=
          notMem_union_right
            (notMem_union_right (notMem_union_right (notMem_union_right hx)))
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        exact castEq
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (b[x]) = (σ * b)[x] from
            sbUpdate_conc σ x (𝐯x) b hxb)
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (b'[x]) = (σ * b')[x] from
            sbUpdate_conc σ x (𝐯x) b' hxb')
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (ih₁ x hxS (liftSb p h₀ hxΓ hxΔ (ih₂ p)))
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        exact castIsTy
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (ih₃ x hxS (liftSb p h₀ hxΓ hxΔ (ih₂ p)))
  | @appCong Γ l l' A A' B B' a a' b b' S _ _ _ _ h₀ h₁ ih₀ ih₁ ih₂ ih₃ ih₄ ih₅ =>
      intro σ Δ p
      refine castEq rfl rfl (sb_conc σ B a).symm ?_
      refine .appCong (S ∪ supp (Δ, B, B')) (ih₀ p) (fun x hx => ?_) (ih₂ p)
        (ih₃ p) (ih₄ p) (fun x hx => ?_)
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        have hxB' : x # B' :=
          notMem_union_right (notMem_union_right (notMem_union_right hx))
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        exact castTyEq
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B'[x]) = (σ * B')[x] from
            sbUpdate_conc σ x (𝐯x) B' hxB')
          (ih₁ x hxS (liftSb p h₀ hxΓ hxΔ (ih₄ p)))
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        exact castIsTy
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (ih₅ x hxS (liftSb p h₀ hxΓ hxΔ (ih₄ p)))
  | idCong _ _ _ ih₀ ih₁ ih₂ =>
      intro σ Δ p
      exact .idCong (ih₀ p) (ih₁ p) (ih₂ p)
  | reflCong _ _ ih₀ ih₁ =>
      intro σ Δ p
      exact .reflCong (ih₀ p) (ih₁ p)
  | @jCong Γ l l' A C C' a a' b b' c c' ee ee' S q₀ q₁ q₂ q₃ q₄ h₀ h₁
      ih₀ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
      intro σ Δ p
      refine castEq rfl rfl (sb_conc₂ σ C b ee).symm ?_
      have key : ∀ x, x # S → x # Δ →
          ((σ ∘/ x ≔ (𝐯x : Tm0)) * (𝐈𝐝 A a (𝐯x) : Ty0) = 𝐈𝐝 (σ * A) (σ * a) (𝐯x)) ∧
          ((Δ ⨟ x ∶ σ * A ⦂ l) ⊢ 𝐈𝐝 (σ * A) (σ * a) (𝐯x) ⦂ l) := by
        intro x hxS hxΔ
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        have hfr := derivFresh q₁ hxΓ
        have hxa : x # a := notMem_union_left hfr
        have hxA : x # A := notMem_union_right (notMem_union_right hfr)
        have eqI : (σ ∘/ x ≔ (𝐯x : Tm0)) * (𝐈𝐝 A a (𝐯x) : Ty0)
            = 𝐈𝐝 (σ * A) (σ * a) (𝐯x) := by
          rw [sbId, updateFresh σ x (𝐯x) A hxA, updateFresh σ x (𝐯x) a hxa,
            sbAtom, Sb.update_eq]
        exact ⟨eqI, castIsTy eqI (ih₆ x hxS (liftSb p h₀ hxΓ hxΔ (ih₅ p)))⟩
      refine .jCong (S ∪ supp (Δ, C, C')) ?_ (ih₁ p) (ih₂ p) ?_ (ih₄ p) (ih₅ p)
        (fun x hx => (key x (notMem_union_left hx)
          (notMem_union_left (notMem_union_right hx))).2)
      · intro x y hfr2
        obtain ⟨hy, hxx, hxy⟩ := Fresh₂.inv hfr2
        have hxS : x # S := notMem_union_left hxx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hxx)
        have hxC : x # C :=
          notMem_union_left (notMem_union_right (notMem_union_right hxx))
        have hxC' : x # C' :=
          notMem_union_right (notMem_union_right (notMem_union_right hxx))
        have hyS : y # S := notMem_union_left hy
        have hyΔ : y # Δ := notMem_union_left (notMem_union_right hy)
        have hyC : y # C :=
          notMem_union_left (notMem_union_right (notMem_union_right hy))
        have hyC' : y # C' :=
          notMem_union_right (notMem_union_right (notMem_union_right hy))
        obtain ⟨eqI, hId⟩ := key x hxS hxΔ
        have hyΓ : y # Γ := (snocOkInv (derivOk (h₁ y hyS))).1
        have pl := liftSb₂ p h₀ (h₁ x hxS) hxΔ (NotMem.union hyΓ (fresh_symm hxy))
          (NotMem.union hyΔ (fresh_symm hxy)) rfl eqI (ih₅ p) hId
        exact castTyEq
          (show ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (C[x][y]) = (σ * C)[x][y]
            from sbUpdate_conc₂ σ x y (𝐯x) (𝐯y) C hxC
              (NotMem.union hyC (fresh_symm hxy)))
          (show ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (C'[x][y])
            = (σ * C')[x][y] from sbUpdate_conc₂ σ x y (𝐯x) (𝐯y) C' hxC'
              (NotMem.union hyC' (fresh_symm hxy)))
          (ih₀ x y (Fresh₂.intro hyS hxS hxy) pl)
      · exact castEq rfl rfl
          (show σ * (C[a][𝐫𝐞𝐟𝐥 a]) = (σ * C)[σ * a][𝐫𝐞𝐟𝐥 (σ * a)] from
            sb_conc₂ σ C a (𝐫𝐞𝐟𝐥 a))
          (ih₃ p)
  | succCong _ ih =>
      intro σ Δ p
      exact .succCong (ih p)
  | @nrecCong Γ l C C' c₀ c₀' a a' cs cs' S q₀ q₁ q₂ _ h ih₀ ih₁ ih₂ ih₃ ih₄ =>
      intro σ Δ p
      refine castEq rfl rfl (sb_conc σ C a).symm ?_
      have key : ∀ x, x # S → x # Δ → x # C →
          (x # Γ) ∧ ((Δ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) ⊢ (σ * C)[x] ⦂ l) := by
        intro x hxS hxΔ hxC
        have hxΓ : x # Γ := (snocOkInv (derivOk (h x hxS))).1
        exact ⟨hxΓ, castIsTy
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] from
            sbUpdate_conc σ x (𝐯x) C hxC)
          (ih₄ x hxS (liftSb p (Deriv.nat (derivOk q₁)) hxΓ hxΔ
            (Deriv.nat (okSb p))))⟩
      refine .nrecCong (S ∪ supp (Δ, C, C', cs, cs')) (fun x hx => ?_) ?_
        (fun x y hfr2 => ?_) (ih₃ p)
        (fun x hx => (key x (notMem_union_left hx)
          (notMem_union_left (notMem_union_right hx))
          (notMem_union_left (notMem_union_right (notMem_union_right hx)))).2)
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxC : x # C :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        have hxC' : x # C' :=
          notMem_union_left
            (notMem_union_right (notMem_union_right (notMem_union_right hx)))
        obtain ⟨hxΓ, _⟩ := key x hxS hxΔ hxC
        exact castTyEq
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] from
            sbUpdate_conc σ x (𝐯x) C hxC)
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C'[x]) = (σ * C')[x] from
            sbUpdate_conc σ x (𝐯x) C' hxC')
          (ih₀ x hxS (liftSb p (Deriv.nat (derivOk q₁)) hxΓ hxΔ
            (Deriv.nat (okSb p))))
      · exact castEq rfl rfl
          (show σ * (C[(𝐳𝐞𝐫𝐨 : Tm0)]) = (σ * C)[(𝐳𝐞𝐫𝐨 : Tm0)] from sb_conc σ C 𝐳𝐞𝐫𝐨)
          (ih₁ p)
      · obtain ⟨hy, hxx, hxy⟩ := Fresh₂.inv hfr2
        have hxS : x # S := notMem_union_left hxx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hxx)
        have hxC : x # C :=
          notMem_union_left (notMem_union_right (notMem_union_right hxx))
        have hxcs : x # cs :=
          notMem_union_left (notMem_union_right (notMem_union_right
            (notMem_union_right (notMem_union_right hxx))))
        have hxcs' : x # cs' :=
          notMem_union_right (notMem_union_right (notMem_union_right
            (notMem_union_right (notMem_union_right hxx))))
        have hyS : y # S := notMem_union_left hy
        have hyΔ : y # Δ := notMem_union_left (notMem_union_right hy)
        have hyC : y # C :=
          notMem_union_left (notMem_union_right (notMem_union_right hy))
        have hycs : y # cs :=
          notMem_union_left (notMem_union_right (notMem_union_right
            (notMem_union_right (notMem_union_right hy))))
        have hycs' : y # cs' :=
          notMem_union_right (notMem_union_right (notMem_union_right
            (notMem_union_right (notMem_union_right hy))))
        obtain ⟨hxΓ, hC⟩ := key x hxS hxΔ hxC
        have hfrS : x # y # S := Fresh₂.intro hyS hxS hxy
        have hyΓx : y # (Γ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) :=
          (snocOkInv (derivOk (q₂ x y hfrS))).1
        have hyx : y ≠ x := (Fset.ne_of_notMem_single hxy).symm
        have eqC : ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) *
            (C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)]) = (σ * C)[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] := by
          rw [sb_conc, updateFresh (σ ∘/ x ≔ (𝐯x : Tm0)) y (𝐯y) C hyC,
            updateFresh σ x (𝐯x) C hxC, sbSucc, sbAtom,
            Sb.update_neq _ _ hyx, Sb.update_eq]
        have pl := liftSb₂ p (Deriv.nat (derivOk q₁)) (h x hxS) hxΔ hyΓx
          (NotMem.union hyΔ (fresh_symm hxy)) (sbNat σ)
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] from
            sbUpdate_conc σ x (𝐯x) C hxC)
          (Deriv.nat (okSb p)) hC
        exact castEq
          (show ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (cs[x][y])
            = (σ * cs)[x][y] from sbUpdate_conc₂ σ x y (𝐯x) (𝐯y) cs hxcs
              (NotMem.union hycs (fresh_symm hxy)))
          (show ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (cs'[x][y])
            = (σ * cs')[x][y] from sbUpdate_conc₂ σ x y (𝐯x) (𝐯y) cs' hxcs'
              (NotMem.union hycs' (fresh_symm hxy)))
          eqC (ih₂ x y hfrS pl)
  | @piBeta Γ l l' A a B b S _ _ h₀ h₁ ih₀ ih₁ ih₂ ih₃ =>
      intro σ Δ p
      refine castEq rfl (sb_conc σ b a).symm (sb_conc σ B a).symm ?_
      refine .piBeta (S ∪ supp (Δ, B, b)) (fun x hx => ?_) (ih₁ p) (ih₂ p)
        (fun x hx => ?_)
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        have hxb : x # b :=
          notMem_union_right (notMem_union_right (notMem_union_right hx))
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        exact castTm
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (b[x]) = (σ * b)[x] from
            sbUpdate_conc σ x (𝐯x) b hxb)
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (ih₀ x hxS (liftSb p h₀ hxΓ hxΔ (ih₂ p)))
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        exact castIsTy
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (ih₃ x hxS (liftSb p h₀ hxΓ hxΔ (ih₂ p)))
  | @idBeta Γ l l' A C a c S q₀ q₁ q₂ h₀ h₁ ih₀ ih₁ ih₂ ih₃ ih₄ =>
      intro σ Δ p
      have eqCa : σ * (C[a][𝐫𝐞𝐟𝐥 a]) = (σ * C)[σ * a][𝐫𝐞𝐟𝐥 (σ * a)] :=
        sb_conc₂ σ C a (𝐫𝐞𝐟𝐥 a)
      refine castEq rfl rfl eqCa.symm ?_
      have key : ∀ x, x # S → x # Δ →
          ((σ ∘/ x ≔ (𝐯x : Tm0)) * (𝐈𝐝 A a (𝐯x) : Ty0) = 𝐈𝐝 (σ * A) (σ * a) (𝐯x)) ∧
          ((Δ ⨟ x ∶ σ * A ⦂ l) ⊢ 𝐈𝐝 (σ * A) (σ * a) (𝐯x) ⦂ l) := by
        intro x hxS hxΔ
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        have hfr := derivFresh q₁ hxΓ
        have hxa : x # a := notMem_union_left hfr
        have hxA : x # A := notMem_union_right hfr
        have eqI : (σ ∘/ x ≔ (𝐯x : Tm0)) * (𝐈𝐝 A a (𝐯x) : Ty0)
            = 𝐈𝐝 (σ * A) (σ * a) (𝐯x) := by
          rw [sbId, updateFresh σ x (𝐯x) A hxA, updateFresh σ x (𝐯x) a hxa,
            sbAtom, Sb.update_eq]
        exact ⟨eqI, castIsTy eqI (ih₄ x hxS (liftSb p h₀ hxΓ hxΔ (ih₃ p)))⟩
      refine .idBeta (S ∪ supp (Δ, C)) ?_ (ih₁ p) (castTm rfl eqCa (ih₂ p)) (ih₃ p)
        (fun x hx => (key x (notMem_union_left hx)
          (notMem_union_left (notMem_union_right hx))).2)
      intro x y hfr2
      obtain ⟨hy, hxx, hxy⟩ := Fresh₂.inv hfr2
      have hxS : x # S := notMem_union_left hxx
      have hxΔ : x # Δ := notMem_union_left (notMem_union_right hxx)
      have hxC : x # C := notMem_union_right (notMem_union_right hxx)
      have hyS : y # S := notMem_union_left hy
      have hyΔ : y # Δ := notMem_union_left (notMem_union_right hy)
      have hyC : y # C := notMem_union_right (notMem_union_right hy)
      obtain ⟨eqI, hId⟩ := key x hxS hxΔ
      have hyΓ : y # Γ := (snocOkInv (derivOk (h₁ y hyS))).1
      have pl := liftSb₂ p h₀ (h₁ x hxS) hxΔ (NotMem.union hyΓ (fresh_symm hxy))
        (NotMem.union hyΔ (fresh_symm hxy)) rfl eqI (ih₃ p) hId
      exact castIsTy
        (show ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (C[x][y]) = (σ * C)[x][y]
          from sbUpdate_conc₂ σ x y (𝐯x) (𝐯y) C hxC
            (NotMem.union hyC (fresh_symm hxy)))
        (ih₀ x y (Fresh₂.intro hyS hxS hxy) pl)
  | @natBeta₀ Γ l C c₀ cs S q₀ q₁ h ih₀ ih₁ ih₂ =>
      intro σ Δ p
      have eqz : σ * (C[(𝐳𝐞𝐫𝐨 : Tm0)]) = (σ * C)[(𝐳𝐞𝐫𝐨 : Tm0)] := sb_conc σ C 𝐳𝐞𝐫𝐨
      refine castEq rfl rfl eqz.symm ?_
      have key : ∀ x, x # S → x # Δ → x # C →
          (x # Γ) ∧ ((Δ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) ⊢ (σ * C)[x] ⦂ l) := by
        intro x hxS hxΔ hxC
        have hxΓ : x # Γ := (snocOkInv (derivOk (h x hxS))).1
        exact ⟨hxΓ, castIsTy
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] from
            sbUpdate_conc σ x (𝐯x) C hxC)
          (ih₂ x hxS (liftSb p (Deriv.nat (derivOk q₀)) hxΓ hxΔ
            (Deriv.nat (okSb p))))⟩
      refine .natBeta₀ (S ∪ supp (Δ, C, cs)) (castTm rfl eqz (ih₀ p))
        (fun x y hfr2 => ?_)
        (fun x hx => (key x (notMem_union_left hx)
          (notMem_union_left (notMem_union_right hx))
          (notMem_union_left (notMem_union_right (notMem_union_right hx)))).2)
      obtain ⟨hy, hxx, hxy⟩ := Fresh₂.inv hfr2
      have hxS : x # S := notMem_union_left hxx
      have hxΔ : x # Δ := notMem_union_left (notMem_union_right hxx)
      have hxC : x # C :=
        notMem_union_left (notMem_union_right (notMem_union_right hxx))
      have hxcs : x # cs :=
        notMem_union_right (notMem_union_right (notMem_union_right hxx))
      have hyS : y # S := notMem_union_left hy
      have hyΔ : y # Δ := notMem_union_left (notMem_union_right hy)
      have hyC : y # C :=
        notMem_union_left (notMem_union_right (notMem_union_right hy))
      have hycs : y # cs :=
        notMem_union_right (notMem_union_right (notMem_union_right hy))
      obtain ⟨hxΓ, hC⟩ := key x hxS hxΔ hxC
      have hfrS : x # y # S := Fresh₂.intro hyS hxS hxy
      have hyΓx : y # (Γ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) :=
        (snocOkInv (derivOk (q₁ x y hfrS))).1
      have hyx : y ≠ x := (Fset.ne_of_notMem_single hxy).symm
      have eqC : ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) *
          (C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)]) = (σ * C)[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] := by
        rw [sb_conc, updateFresh (σ ∘/ x ≔ (𝐯x : Tm0)) y (𝐯y) C hyC,
          updateFresh σ x (𝐯x) C hxC, sbSucc, sbAtom,
          Sb.update_neq _ _ hyx, Sb.update_eq]
      have pl := liftSb₂ p (Deriv.nat (derivOk q₀)) (h x hxS) hxΔ hyΓx
        (NotMem.union hyΔ (fresh_symm hxy)) (sbNat σ)
        (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] from
          sbUpdate_conc σ x (𝐯x) C hxC)
        (Deriv.nat (okSb p)) hC
      exact castTm
        (show ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (cs[x][y])
          = (σ * cs)[x][y] from sbUpdate_conc₂ σ x y (𝐯x) (𝐯y) cs hxcs
            (NotMem.union hycs (fresh_symm hxy)))
        eqC (ih₁ x y hfrS pl)
  | @natBetaS Γ l C c₀ a cs S q₀ q₁ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      intro σ Δ p
      have eqz : σ * (C[(𝐳𝐞𝐫𝐨 : Tm0)]) = (σ * C)[(𝐳𝐞𝐫𝐨 : Tm0)] := sb_conc σ C 𝐳𝐞𝐫𝐨
      refine castEq rfl
        (show σ * (cs[a][𝐧𝐫𝐞𝐜 C c₀ cs a])
          = (σ * cs)[σ * a][𝐧𝐫𝐞𝐜 (σ * C) (σ * c₀) (σ * cs) (σ * a)] from
          sb_conc₂ σ cs a (𝐧𝐫𝐞𝐜 C c₀ cs a)).symm
        (show σ * (C[𝐬𝐮𝐜𝐜 a]) = (σ * C)[𝐬𝐮𝐜𝐜 (σ * a)] from
          sb_conc σ C (𝐬𝐮𝐜𝐜 a)).symm ?_
      have key : ∀ x, x # S → x # Δ → x # C →
          (x # Γ) ∧ ((Δ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) ⊢ (σ * C)[x] ⦂ l) := by
        intro x hxS hxΔ hxC
        have hxΓ : x # Γ := (snocOkInv (derivOk (h x hxS))).1
        exact ⟨hxΓ, castIsTy
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] from
            sbUpdate_conc σ x (𝐯x) C hxC)
          (ih₃ x hxS (liftSb p (Deriv.nat (derivOk q₀)) hxΓ hxΔ
            (Deriv.nat (okSb p))))⟩
      refine .natBetaS (S ∪ supp (Δ, C, cs)) (castTm rfl eqz (ih₀ p))
        (fun x y hfr2 => ?_) (ih₂ p)
        (fun x hx => (key x (notMem_union_left hx)
          (notMem_union_left (notMem_union_right hx))
          (notMem_union_left (notMem_union_right (notMem_union_right hx)))).2)
      obtain ⟨hy, hxx, hxy⟩ := Fresh₂.inv hfr2
      have hxS : x # S := notMem_union_left hxx
      have hxΔ : x # Δ := notMem_union_left (notMem_union_right hxx)
      have hxC : x # C :=
        notMem_union_left (notMem_union_right (notMem_union_right hxx))
      have hxcs : x # cs :=
        notMem_union_right (notMem_union_right (notMem_union_right hxx))
      have hyS : y # S := notMem_union_left hy
      have hyΔ : y # Δ := notMem_union_left (notMem_union_right hy)
      have hyC : y # C :=
        notMem_union_left (notMem_union_right (notMem_union_right hy))
      have hycs : y # cs :=
        notMem_union_right (notMem_union_right (notMem_union_right hy))
      obtain ⟨hxΓ, hC⟩ := key x hxS hxΔ hxC
      have hfrS : x # y # S := Fresh₂.intro hyS hxS hxy
      have hyΓx : y # (Γ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) :=
        (snocOkInv (derivOk (q₁ x y hfrS))).1
      have hyx : y ≠ x := (Fset.ne_of_notMem_single hxy).symm
      have eqC : ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) *
          (C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)]) = (σ * C)[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] := by
        rw [sb_conc, updateFresh (σ ∘/ x ≔ (𝐯x : Tm0)) y (𝐯y) C hyC,
          updateFresh σ x (𝐯x) C hxC, sbSucc, sbAtom,
          Sb.update_neq _ _ hyx, Sb.update_eq]
      have pl := liftSb₂ p (Deriv.nat (derivOk q₀)) (h x hxS) hxΔ hyΓx
        (NotMem.union hyΔ (fresh_symm hxy)) (sbNat σ)
        (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] from
          sbUpdate_conc σ x (𝐯x) C hxC)
        (Deriv.nat (okSb p)) hC
      exact castTm
        (show ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (cs[x][y])
          = (σ * cs)[x][y] from sbUpdate_conc₂ σ x y (𝐯x) (𝐯y) cs hxcs
            (NotMem.union hycs (fresh_symm hxy)))
        eqC (ih₁ x y hfrS pl)
  | @piEta Γ l l' A B b b' S q₀ q₁ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      intro σ Δ p
      refine .piEta (S ∪ supp Δ) (ih₀ p) (ih₁ p) (fun x hx => ?_) (ih₃ p)
      have hxS : x # S := notMem_union_left hx
      have hxΔ : x # Δ := notMem_union_right hx
      have hxΓ : x # Γ := (snocOkInv (derivOk (q₂ x hxS))).1
      have hfr := derivFresh q₀ hxΓ
      have hxb : x # b := notMem_union_left hfr
      have hxA : x # A := notMem_union_left (notMem_union_right hfr)
      have hxB : x # B :=
        notMem_union_left (notMem_union_right (notMem_union_right hfr))
      have hxb' : x # b' := notMem_union_left (derivFresh q₁ hxΓ)
      have eqApp : ∀ (d : Tm0), x # d →
          (σ ∘/ x ≔ (𝐯x : Tm0)) * (d ∙[ A, B ] 𝐯x)
            = (σ * d) ∙[ σ * A, σ * B ] (𝐯x) := by
        intro d hxd
        rw [sbApp, updateFresh σ x (𝐯x) d hxd, updateFresh σ x (𝐯x) A hxA,
          updateFresh σ x (𝐯x) B hxB, sbAtom, Sb.update_eq]
      exact castEq (eqApp b hxb) (eqApp b' hxb')
        (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
          sbUpdate_conc σ x (𝐯x) B hxB)
        (ih₂ x hxS (liftSb p h hxΓ hxΔ (ih₃ p)))

/-! ## Conversion for substitutions is reflexive -/

theorem sbEqRefl {σ : Sb sig} {Γ Γ' : Cx} (p : Γ' ⊢ˢ σ ∶ Γ) : Γ' ⊢ˢ σ ＝ σ ∶ Γ := by
  induction p with
  | nil q => exact .nil q
  | snoc _ q₁ q₂ q₃ ih => exact .snoc ih q₁ (.refl q₂) q₃

/-! ## Properties of substitution update -/

theorem sbUpdate {l : Lvl} {Γ Γ' : Cx} {σ : Sb sig} {A : Ty0} {a : Tm0} {x : Atom}
    (p : Γ' ⊢ˢ σ ∶ Γ) (q : Γ' ⊢ a ∶ σ * A ⦂ l) (hx : x # Γ) (h : Γ ⊢ A ⦂ l) :
    Γ' ⊢ˢ (σ ∘/ x ≔ a) ∶ (Γ ⨟ x ∶ A ⦂ l) := by
  refine .snoc (sbExt p fun _ r => updateNeqDom hx r) h ?_ hx
  exact castTm (Sb.update_eq σ x a).symm
    (updateFresh σ x a A (notMem_union_left (derivFresh h hx))).symm q

theorem sbEqUpdate {l : Lvl} {Γ Γ' : Cx} {σ σ' : Sb sig} {A : Ty0} {a a' : Tm0}
    {x : Atom} (p : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) (q : Γ' ⊢ a ＝ a' ∶ σ * A ⦂ l) (hx : x # Γ)
    (h : Γ ⊢ A ⦂ l) :
    Γ' ⊢ˢ (σ ∘/ x ≔ a) ＝ (σ' ∘/ x ≔ a') ∶ (Γ ⨟ x ∶ A ⦂ l) := by
  refine .snoc
    (sbEqExt p (fun _ r => updateNeqDom hx r) (fun _ r => updateNeqDom hx r)) h ?_ hx
  exact castEq (Sb.update_eq σ x a).symm (Sb.update_eq σ' x a').symm
    (updateFresh σ x a A (notMem_union_left (derivFresh h hx))).symm q

theorem ssbUpdate {l : Lvl} {Γ : Cx} {A : Ty0} {a : Tm0} {x : Atom}
    (q : Γ ⊢ a ∶ A ⦂ l) (hx : x # Γ) (h : Γ ⊢ A ⦂ l) :
    Γ ⊢ˢ (x ≔ a) ∶ (Γ ⨟ x ∶ A ⦂ l) := by
  refine sbUpdate (σ := Sb.id) (idSbTyping (derivOk q)) ?_ hx h
  exact castTm rfl (sbUnit A).symm q

theorem ssbEqUpdate {l : Lvl} {Γ : Cx} {A : Ty0} {a a' : Tm0} {x : Atom}
    (q : Γ ⊢ a ＝ a' ∶ A ⦂ l) (hx : x # Γ) (h : Γ ⊢ A ⦂ l) :
    Γ ⊢ˢ (x ≔ a) ＝ (x ≔ a') ∶ (Γ ⨟ x ∶ A ⦂ l) := by
  refine sbEqUpdate (σ := Sb.id) (σ' := Sb.id)
    (sbEqRefl (idSbTyping (derivOk q))) ?_ hx h
  exact castEq rfl rfl (sbUnit A).symm q

theorem ssbUpdate₂ {l l' : Lvl} {Γ : Cx} {x y : Atom} {a b : Tm0} {A B : Ty0}
    (q₀ : Γ ⊢ a ∶ A ⦂ l) (q₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B ⦂ l')
    (q₂ : Γ ⊢ b ∶ (x ≔ a) * B ⦂ l') (q₃ : y # (Γ, x)) :
    Γ ⊢ˢ ((x ≔ a) ∘/ y ≔ b) ∶ (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') := by
  obtain ⟨hx, hA, _⟩ := snocOkInv (derivOk q₁)
  exact sbUpdate (ssbUpdate q₀ hx hA) q₂ q₃ q₁

theorem ssbEqUpdate₂ {l l' : Lvl} {Γ : Cx} {x y : Atom} {a a' b b' : Tm0}
    {A B : Ty0} (q₀ : Γ ⊢ a ＝ a' ∶ A ⦂ l) (q₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B ⦂ l')
    (q₂ : Γ ⊢ b ＝ b' ∶ (x ≔ a) * B ⦂ l') (q₃ : y # (Γ, x)) :
    Γ ⊢ˢ ((x ≔ a) ∘/ y ≔ b) ＝ ((x ≔ a') ∘/ y ≔ b') ∶
      (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') := by
  obtain ⟨hx, hA, _⟩ := snocOkInv (derivOk q₁)
  exact sbEqUpdate (ssbEqUpdate q₀ hx hA) q₂ q₃ q₁

/-! ## Lifting substitutions, again -/

theorem liftSbInv {l : Lvl} {σ : Sb sig} {Γ Γ' : Cx} {A : Ty0} {x x' : Atom}
    (q₀ : Γ' ⊢ˢ σ ∶ Γ) (q₁ : Γ ⊢ A ⦂ l) (q₂ : x # Γ) (q₃ : x' # Γ') :
    (Γ' ⨟ x' ∶ σ * A ⦂ l) ⊢ˢ (σ ∘/ x ≔ 𝐯x') ∶ (Γ ⨟ x ∶ A ⦂ l) :=
  liftSb q₀ q₁ q₂ q₃ (sbDeriv q₀ q₁)

theorem liftEqSb {l : Lvl} {σ σ' : Sb sig} {Γ Γ' : Cx} {A : Ty0} {x x' : Atom}
    (p : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) (q : Γ ⊢ A ⦂ l) (hx : x # Γ) (hx' : x' # Γ')
    (h : Γ' ⊢ˢ σ ∶ Γ) :
    (Γ' ⨟ x' ∶ σ * A ⦂ l) ⊢ˢ (σ ∘/ x ≔ 𝐯x') ＝ (σ' ∘/ x ≔ 𝐯x') ∶
      (Γ ⨟ x ∶ A ⦂ l) := by
  have hσA : Γ' ⊢ σ * A ⦂ l := sbDeriv h q
  have p' : Γ' ⊢ˢ (σ ∘/ x ≔ (𝐯x' : Tm0)) ＝ (σ' ∘/ x ≔ (𝐯x' : Tm0)) ∶ Γ :=
    sbEqExt p (fun _ r => updateNeqDom hx r) (fun _ r => updateNeqDom hx r)
  refine .snoc (wkEqSb x' hσA p' hx') q ?_ hx
  have hxA : x # A := notMem_union_left (derivFresh q hx)
  rw [updateFresh σ x (𝐯x') A hxA, Sb.update_eq, Sb.update_eq]
  exact .refl (.var (okSnoc hσA hx') .new)

theorem liftEqSb₂ {l l' : Lvl} {x y x' y' : Atom} {σ σ' : Sb sig} {Γ Γ' : Cx}
    {A A' B B' : Ty0} (q₀ : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) (q₁ : Γ ⊢ A ⦂ l)
    (q₂ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B ⦂ l') (q₃ : x' # Γ') (q₄ : y # (Γ, x))
    (q₅ : y' # (Γ', x')) (e : σ * A = A') (e' : (σ ∘/ x ≔ 𝐯x') * B = B')
    (h : Γ' ⊢ˢ σ ∶ Γ) :
    (Γ' ⨟ x' ∶ A' ⦂ l ⨟ y' ∶ B' ⦂ l') ⊢ˢ ((σ ∘/ x ≔ 𝐯x') ∘/ y ≔ 𝐯y') ＝
      ((σ' ∘/ x ≔ 𝐯x') ∘/ y ≔ 𝐯y') ∶ (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') := by
  subst e; subst e'
  obtain ⟨hx, _, _⟩ := snocOkInv (derivOk q₂)
  exact liftEqSb (liftEqSb q₀ q₁ hx q₃ h) q₂ q₄ q₅ (liftSbInv h q₁ hx q₃)

/-! ## Action of convertible substitutions -/

/-- The statement proved by induction for `eqSbTm`.  Agda's `＝sbTm` only has clauses
for the *typing* constructors, because its statement forces the judgement to be of the
form `a ∶ A ⦂ l`; Lean's `Deriv.rec` demands all thirty cases, so the induction runs
for this predicate, which is vacuously true on conversion judgements. -/
private def eqSbTmGoal (Δ : Cx) (σ σ' : Sb sig) : Jg → Prop
  | .ty a A l => Δ ⊢ σ * a ＝ σ' * a ∶ σ * A ⦂ l
  | .eq _ _ _ _ => True

/-- The induction behind `eqSbTm`; see `eqSbTmGoal`. -/
private theorem eqSbTmAux {Γ : Cx} {J : Jg} (q : Γ ⊢ J) {σ σ' : Sb sig} {Δ : Cx}
    (p : Δ ⊢ˢ σ ＝ σ' ∶ Γ) (h : Δ ⊢ˢ σ ∶ Γ) : eqSbTmGoal Δ σ σ' J := by
  revert σ σ' Δ
  induction q using Deriv.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc => trivial
  | conv _ q₁ ih₀ _ =>
      intro σ σ' Δ p hs
      exact .eqConv (ih₀ p hs) (sbDeriv hs q₁)
  | var _ q₁ _ =>
      intro σ σ' Δ p hs
      exact castEq (sbAtom σ _).symm (sbAtom σ' _).symm rfl (sbVarEq p q₁)
  | @univ Γ l _ _ =>
      intro σ σ' Δ p hs
      exact castEq (sbU σ l).symm (sbU σ' l).symm (sbU σ (l + 1)).symm
        (Deriv.refl (Deriv.univ (okSbEq p)))
  | @pi Γ l l' A B S q₀ q₁ ih₀ ih₁ =>
      intro σ σ' Δ p hs
      refine .piCong (S ∪ supp (Δ, B)) (ih₀ p hs) (fun x hx => ?_) (sbDeriv hs q₀)
      have hxS : x # S := notMem_union_left hx
      have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
      have hxB : x # B := notMem_union_right (notMem_union_right hx)
      have hxΓ : x # Γ := (snocOkInv (derivOk (q₁ x hxS))).1
      exact castTyEq
        (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
          sbUpdate_conc σ x (𝐯x) B hxB)
        (show (σ' ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ' * B)[x] from
          sbUpdate_conc σ' x (𝐯x) B hxB)
        (ih₁ x hxS (liftEqSb p q₀ hxΓ hxΔ hs) (liftSbInv hs q₀ hxΓ hxΔ))
  | @lam Γ l l' A B b S q₀ h₀ h₁ ih₀ ih₁ ih₂ =>
      intro σ σ' Δ p hs
      refine .lamCong (S ∪ supp (Δ, B, b)) (ih₁ p hs) (fun x hx => ?_)
        (sbDeriv hs h₀) (fun x hx => ?_)
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        have hxb : x # b :=
          notMem_union_right (notMem_union_right (notMem_union_right hx))
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        exact castEq
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (b[x]) = (σ * b)[x] from
            sbUpdate_conc σ x (𝐯x) b hxb)
          (show (σ' ∘/ x ≔ (𝐯x : Tm0)) * (b[x]) = (σ' * b)[x] from
            sbUpdate_conc σ' x (𝐯x) b hxb)
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (ih₀ x hxS (liftEqSb p h₀ hxΓ hxΔ hs) (liftSbInv hs h₀ hxΓ hxΔ))
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        exact castIsTy
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (sbDeriv (liftSbInv hs h₀ hxΓ hxΔ) (h₁ x hxS))
  | @app Γ l l' A B a b S q₀ q₁ q₂ hh ih₀ ih₁ ih₂ ih₃ =>
      intro σ σ' Δ p hs
      refine castEq rfl rfl (sb_conc σ B a).symm ?_
      refine .appCong (S ∪ supp (Δ, B)) (ih₃ p hs) (fun x hx => ?_) (ih₀ p hs)
        (ih₁ p hs) (sbDeriv hs hh) (fun x hx => ?_)
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B := notMem_union_right (notMem_union_right hx)
        have hxΓ : x # Γ := (snocOkInv (derivOk (q₂ x hxS))).1
        exact castTyEq
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (show (σ' ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ' * B)[x] from
            sbUpdate_conc σ' x (𝐯x) B hxB)
          (ih₂ x hxS (liftEqSb p hh hxΓ hxΔ hs) (liftSbInv hs hh hxΓ hxΔ))
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxB : x # B := notMem_union_right (notMem_union_right hx)
        have hxΓ : x # Γ := (snocOkInv (derivOk (q₂ x hxS))).1
        exact castIsTy
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (B[x]) = (σ * B)[x] from
            sbUpdate_conc σ x (𝐯x) B hxB)
          (sbDeriv (liftSbInv hs hh hxΓ hxΔ) (q₂ x hxS))
  | idF _ _ _ ih₀ ih₁ ih₂ =>
      intro σ σ' Δ p hs
      exact .idCong (ih₂ p hs) (ih₀ p hs) (ih₁ p hs)
  | reflI _ hh ih₀ _ =>
      intro σ σ' Δ p hs
      exact .reflCong (ih₀ p hs) (sbDeriv hs hh)
  | @j Γ l l' A C a b c ee S q₀ q₁ q₂ q₃ q₄ h₀ h₁ ih₀ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
      intro σ σ' Δ p hs
      refine castEq rfl rfl (sb_conc₂ σ C b ee).symm ?_
      have key : ∀ x, x # S → x # Δ →
          ((σ ∘/ x ≔ (𝐯x : Tm0)) * (𝐈𝐝 A a (𝐯x) : Ty0) = 𝐈𝐝 (σ * A) (σ * a) (𝐯x)) ∧
          ((Δ ⨟ x ∶ σ * A ⦂ l) ⊢ 𝐈𝐝 (σ * A) (σ * a) (𝐯x) ⦂ l) := by
        intro x hxS hxΔ
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        have hfr := derivFresh q₁ hxΓ
        have hxa : x # a := notMem_union_left hfr
        have hxA : x # A := notMem_union_right hfr
        have eqI : (σ ∘/ x ≔ (𝐯x : Tm0)) * (𝐈𝐝 A a (𝐯x) : Ty0)
            = 𝐈𝐝 (σ * A) (σ * a) (𝐯x) := by
          rw [sbId, updateFresh σ x (𝐯x) A hxA, updateFresh σ x (𝐯x) a hxa,
            sbAtom, Sb.update_eq]
        exact ⟨eqI, castIsTy eqI (sbDeriv (liftSbInv hs h₀ hxΓ hxΔ) (h₁ x hxS))⟩
      refine .jCong (S ∪ supp (Δ, C)) ?_ (ih₁ p hs) (ih₂ p hs) ?_ (ih₄ p hs)
        (sbDeriv hs h₀)
        (fun x hx => (key x (notMem_union_left hx)
          (notMem_union_left (notMem_union_right hx))).2)
      · intro x y hfr2
        obtain ⟨hy, hxx, hxy⟩ := Fresh₂.inv hfr2
        have hxS : x # S := notMem_union_left hxx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hxx)
        have hxC : x # C := notMem_union_right (notMem_union_right hxx)
        have hyS : y # S := notMem_union_left hy
        have hyΔ : y # Δ := notMem_union_left (notMem_union_right hy)
        have hyC : y # C := notMem_union_right (notMem_union_right hy)
        obtain ⟨eqI, hId⟩ := key x hxS hxΔ
        have hyΓ : y # Γ := (snocOkInv (derivOk (h₁ y hyS))).1
        have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
        have pe := liftEqSb₂ p h₀ (h₁ x hxS) hxΔ (NotMem.union hyΓ (fresh_symm hxy))
          (NotMem.union hyΔ (fresh_symm hxy)) rfl eqI hs
        have pl := liftSb₂ hs h₀ (h₁ x hxS) hxΔ (NotMem.union hyΓ (fresh_symm hxy))
          (NotMem.union hyΔ (fresh_symm hxy)) rfl eqI (sbDeriv hs h₀) hId
        exact castTyEq
          (show ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (C[x][y]) = (σ * C)[x][y]
            from sbUpdate_conc₂ σ x y (𝐯x) (𝐯y) C hxC
              (NotMem.union hyC (fresh_symm hxy)))
          (show ((σ' ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (C[x][y])
            = (σ' * C)[x][y] from sbUpdate_conc₂ σ' x y (𝐯x) (𝐯y) C hxC
              (NotMem.union hyC (fresh_symm hxy)))
          (ih₀ x y (Fresh₂.intro hyS hxS hxy) pe pl)
      · exact castEq rfl rfl
          (show σ * (C[a][𝐫𝐞𝐟𝐥 a]) = (σ * C)[σ * a][𝐫𝐞𝐟𝐥 (σ * a)] from
            sb_conc₂ σ C a (𝐫𝐞𝐟𝐥 a))
          (ih₃ p hs)
  | nat _ =>
      intro σ σ' Δ p hs
      exact castEq (sbNat σ).symm (sbNat σ').symm (sbU σ 0).symm
        (Deriv.refl (Deriv.nat (okSbEq p)))
  | zero _ =>
      intro σ σ' Δ p hs
      exact castEq (sbZero σ).symm (sbZero σ').symm (sbNat σ).symm
        (Deriv.refl (Deriv.zero (okSbEq p)))
  | succ _ ih =>
      intro σ σ' Δ p hs
      exact .succCong (ih p hs)
  | @nrec Γ l C c₀ a cs S q₀ q₁ q₂ hh ih₀ ih₁ ih₂ ih₃ =>
      intro σ σ' Δ p hs
      refine castEq rfl rfl (sb_conc σ C a).symm ?_
      have key : ∀ x, x # S → x # Δ → x # C →
          (x # Γ) ∧ ((Δ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) ⊢ (σ * C)[x] ⦂ l) := by
        intro x hxS hxΔ hxC
        have hxΓ : x # Γ := (snocOkInv (derivOk (hh x hxS))).1
        exact ⟨hxΓ, castIsTy
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] from
            sbUpdate_conc σ x (𝐯x) C hxC)
          (sbDeriv (liftSbInv hs (Deriv.nat (sbOk hs)) hxΓ hxΔ) (hh x hxS))⟩
      refine .nrecCong (S ∪ supp (Δ, C, cs)) (fun x hx => ?_) ?_
        (fun x y hfr2 => ?_) (ih₂ p hs)
        (fun x hx => (key x (notMem_union_left hx)
          (notMem_union_left (notMem_union_right hx))
          (notMem_union_left (notMem_union_right (notMem_union_right hx)))).2)
      · have hxS : x # S := notMem_union_left hx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hx)
        have hxC : x # C :=
          notMem_union_left (notMem_union_right (notMem_union_right hx))
        obtain ⟨hxΓ, _⟩ := key x hxS hxΔ hxC
        exact castTyEq
          (show (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] from
            sbUpdate_conc σ x (𝐯x) C hxC)
          (show (σ' ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ' * C)[x] from
            sbUpdate_conc σ' x (𝐯x) C hxC)
          (ih₃ x hxS (liftEqSb p (Deriv.nat (sbOk hs)) hxΓ hxΔ hs)
            (liftSbInv hs (Deriv.nat (sbOk hs)) hxΓ hxΔ))
      · exact castEq rfl rfl
          (show σ * (C[(𝐳𝐞𝐫𝐨 : Tm0)]) = (σ * C)[(𝐳𝐞𝐫𝐨 : Tm0)] from sb_conc σ C 𝐳𝐞𝐫𝐨)
          (ih₀ p hs)
      · obtain ⟨hy, hxx, hxy⟩ := Fresh₂.inv hfr2
        have hxS : x # S := notMem_union_left hxx
        have hxΔ : x # Δ := notMem_union_left (notMem_union_right hxx)
        have hxC : x # C :=
          notMem_union_left (notMem_union_right (notMem_union_right hxx))
        have hxcs : x # cs :=
          notMem_union_right (notMem_union_right (notMem_union_right hxx))
        have hyS : y # S := notMem_union_left hy
        have hyΔ : y # Δ := notMem_union_left (notMem_union_right hy)
        have hyC : y # C :=
          notMem_union_left (notMem_union_right (notMem_union_right hy))
        have hycs : y # cs :=
          notMem_union_right (notMem_union_right (notMem_union_right hy))
        obtain ⟨hxΓ, hC⟩ := key x hxS hxΔ hxC
        have hfrS : x # y # S := Fresh₂.intro hyS hxS hxy
        have hyΓx : y # (Γ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) :=
          (snocOkInv (derivOk (q₁ x y hfrS))).1
        have hyx : y ≠ x := (Fset.ne_of_notMem_single hxy).symm
        have eqC : ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) *
            (C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)]) = (σ * C)[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] := by
          rw [sb_conc, updateFresh (σ ∘/ x ≔ (𝐯x : Tm0)) y (𝐯y) C hyC,
            updateFresh σ x (𝐯x) C hxC, sbSucc, sbAtom,
            Sb.update_neq _ _ hyx, Sb.update_eq]
        have eqCx : (σ ∘/ x ≔ (𝐯x : Tm0)) * (C[x]) = (σ * C)[x] :=
          sbUpdate_conc σ x (𝐯x) C hxC
        have pe := liftEqSb₂ p (Deriv.nat (sbOk hs)) (hh x hxS) hxΔ hyΓx
          (NotMem.union hyΔ (fresh_symm hxy)) (sbNat σ) eqCx hs
        have pl := liftSb₂ hs (Deriv.nat (sbOk hs)) (hh x hxS) hxΔ hyΓx
          (NotMem.union hyΔ (fresh_symm hxy)) (sbNat σ) eqCx
          (Deriv.nat (okSb hs)) hC
        exact castEq
          (show ((σ ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (cs[x][y])
            = (σ * cs)[x][y] from sbUpdate_conc₂ σ x y (𝐯x) (𝐯y) cs hxcs
              (NotMem.union hycs (fresh_symm hxy)))
          (show ((σ' ∘/ x ≔ (𝐯x : Tm0)) ∘/ y ≔ (𝐯y : Tm0)) * (cs[x][y])
            = (σ' * cs)[x][y] from sbUpdate_conc₂ σ' x y (𝐯x) (𝐯y) cs hxcs
              (NotMem.union hycs (fresh_symm hxy)))
          eqC (ih₁ x y hfrS pe pl)
  | refl => intro _ _ _ _ _; trivial
  | symm => intro _ _ _ _ _; trivial
  | trans => intro _ _ _ _ _; trivial
  | eqConv => intro _ _ _ _ _; trivial
  | piCong => intro _ _ _ _ _; trivial
  | lamCong => intro _ _ _ _ _; trivial
  | appCong => intro _ _ _ _ _; trivial
  | idCong => intro _ _ _ _ _; trivial
  | reflCong => intro _ _ _ _ _; trivial
  | jCong => intro _ _ _ _ _; trivial
  | succCong => intro _ _ _ _ _; trivial
  | nrecCong => intro _ _ _ _ _; trivial
  | piBeta => intro _ _ _ _ _; trivial
  | idBeta => intro _ _ _ _ _; trivial
  | natBeta₀ => intro _ _ _ _ _; trivial
  | natBetaS => intro _ _ _ _ _; trivial
  | piEta => intro _ _ _ _ _; trivial

theorem eqSbTm {l : Lvl} {σ σ' : Sb sig} {Δ Γ : Cx} {A : Ty0} {a : Tm0}
    (p : Δ ⊢ˢ σ ＝ σ' ∶ Γ) (q : Γ ⊢ a ∶ A ⦂ l) (h : Δ ⊢ˢ σ ∶ Γ) :
    Δ ⊢ σ * a ＝ σ' * a ∶ σ * A ⦂ l := eqSbTmAux q p h

/-! ## Renaming provable judgements is a special case of substitution -/

theorem rnDeriv {ρ : Rn} {Δ Γ : Cx} {J : Jg} (p : Δ ⊢ʳ ρ ∶ Γ) (q : Γ ⊢ J) :
    Δ ⊢ ρ * J := sbDeriv p q

theorem rnSnoc {Γ : Cx} {x x' : Atom} {A : Ty0} {l : Lvl} {J : Jg}
    (q : (Γ ⨟ x ∶ A ⦂ l) ⊢ J) (hx' : x' # Γ) :
    (Γ ⨟ x' ∶ A ⦂ l) ⊢ (x ≔ 𝐯x') * J := by
  obtain ⟨hx, hA, hΓ⟩ := snocOkInv (derivOk q)
  have pl := liftSbInv (σ := Sb.id) (idSbTyping hΓ) hA hx hx'
  rw [sbUnit] at pl
  exact sbDeriv pl q

theorem rnSnoc₂ {Γ : Cx} {x x' y y' : Atom} {A B : Ty0} {l l' : Lvl} {J : Jg}
    (q : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢ J) (hx' : x' # Γ) (hy' : y' # (x', Γ)) :
    (Γ ⨟ x' ∶ A ⦂ l ⨟ y' ∶ (x ≔ 𝐯x') * B ⦂ l') ⊢ ((x ≔ 𝐯x') ∘/ y ≔ 𝐯y') * J := by
  obtain ⟨hy, hB, hOk⟩ := snocOkInv (derivOk q)
  obtain ⟨hx, hA, hΓ⟩ := snocOkInv hOk
  have hy'x' : y' # x' := notMem_union_left hy'
  have hy'Γ : y' # Γ := notMem_union_right hy'
  have pl := liftSbInv (σ := Sb.id) (idSbTyping hΓ) hA hx hx'
  rw [sbUnit] at pl
  exact sbDeriv (liftSb₂ (idSbTyping hΓ) hA hB hx' hy
    (NotMem.union hy'Γ hy'x') (sbUnit A) rfl hA (sbDeriv pl hB)) q

end MLTT

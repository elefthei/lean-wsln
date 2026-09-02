import MLTT.Substitution

/-!
# Further admissible properties of the type system

Port of `agda-code/agda/MLTT/Admissible.agda`.
-/

namespace MLTT

open WSLN
open Fset

/-! ## Plumbing with no Agda counterpart -/

/-- Universes have empty support; Agda gets this from `∉∅`. -/
private theorem freshU {n : Nat} (x : Atom) (l : Lvl) : x # (𝐔 l : Ty n) :=
  Fset.NotMem.empty

/-! ## Reflexivity of context conversion -/

theorem cxRefl {Γ : Cx} (p : Ok Γ) : ⊢ Γ ＝ Γ := by
  revert p
  induction Γ with
  | nil => intro _; exact .nil
  | snoc Γ' x A l ih =>
      intro p
      cases p with
      | snoc q₀ q₁ hh => exact .snoc (ih hh) (.refl q₀) (NotMem.union q₁ q₁) q₀ q₀

/-! ## Change context up to conversion -/

theorem eqIdSb {Γ Γ' : Cx} (p : ⊢ Γ' ＝ Γ) : Γ' ⊢ˢ Sb.id ∶ Γ := by
  induction p with
  | nil => exact .nil .nil
  | @snoc l Γ₁ Γ₂ A A' x q₀ q₁ q₂ h₀ h₁ ih =>
      have hx₁ : x # Γ₁ := notMem_union_left q₂
      have hx₂ : x # Γ₂ := notMem_union_right q₂
      refine .snoc (wkSb x h₀ ih hx₁) h₁ ?_ hx₂
      rw [sbUnit]
      exact .conv (.var (okSnoc h₀ hx₁) .new) (wkDeriv (wkProj h₀ hx₁) q₁)

theorem eqDeriv {Γ Γ' : Cx} {J : Jg} (q : Γ ⊢ J) (q' : ⊢ Γ' ＝ Γ) : Γ' ⊢ J := by
  have h := sbDeriv (eqIdSb q') q
  rwa [sbUnitJg] at h

/-- The last premise is a helper hypothesis. -/
theorem snocEqDeriv {Γ : Cx} {x : Atom} {A A' : Ty0} {l : Lvl} {J : Jg}
    (q : Γ ⊢ A' ＝ A ⦂ l) (q' : (Γ ⨟ x ∶ A ⦂ l) ⊢ J) (h : Γ ⊢ A' ⦂ l) :
    (Γ ⨟ x ∶ A' ⦂ l) ⊢ J := by
  obtain ⟨hxΓ, hA, hΓ⟩ := snocOkInv (derivOk q')
  exact eqDeriv q' (.snoc (cxRefl hΓ) q (NotMem.union hxΓ hxΓ) h hA)

/-! ## Substitution properties of concretion -/

theorem concTm {l l' : Lvl} {Γ : Cx} {A : Ty0} {a : Tm0} (B : Ty 1) (b : Tm 1)
    (x : Atom) (p : (Γ ⨟ x ∶ A ⦂ l) ⊢ b[x] ∶ B[x] ⦂ l') (q : Γ ⊢ a ∶ A ⦂ l)
    (hx : x # (B, b)) : Γ ⊢ b[a] ∶ B[a] ⦂ l' := by
  have hxB : x # B := notMem_union_left hx
  have hxb : x # b := notMem_union_right hx
  obtain ⟨hxΓ, hA, _⟩ := snocOkInv (derivOk p)
  exact castTm (ssb_conc x a b hxb) (ssb_conc x a B hxB)
    (sbDeriv (ssbUpdate q hxΓ hA) p)

theorem concTmInf {l l' : Lvl} {Γ : Cx} {A : Ty0} {a : Tm0} (B : Ty 1) (b : Tm 1)
    (S : Fset) (q₀ : ∀ x, x # S → (Γ ⨟ x ∶ A ⦂ l) ⊢ b[x] ∶ B[x] ⦂ l')
    (q₁ : Γ ⊢ a ∶ A ⦂ l) : Γ ⊢ b[a] ∶ B[a] ⦂ l' := by
  obtain ⟨x, hx⟩ := fresh (S, (B, b))
  exact concTm B b x (q₀ x (notMem_union_left hx)) q₁ (notMem_union_right hx)

/-- The last three premises are helpers. -/
theorem concEqTy {l l' : Lvl} {Γ : Cx} {A : Ty0} {a a' : Tm0} (B B' : Ty 1) (x : Atom)
    (q₀ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ＝ B'[x] ⦂ l') (q₁ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₂ : x # (B, B')) (h₀ : Γ ⊢ a ∶ A ⦂ l) (h₁ : Γ ⊢ a' ∶ A ⦂ l)
    (h₂ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l') : Γ ⊢ B[a] ＝ B'[a'] ⦂ l' := by
  have hxB : x # B := notMem_union_left q₂
  have hxB' : x # B' := notMem_union_right q₂
  obtain ⟨hxΓ, hA, _⟩ := snocOkInv (derivOk q₀)
  have qa : Γ ⊢ B[a] ＝ B[a'] ⦂ l' :=
    castTyEq (ssb_conc x a B hxB) (ssb_conc x a' B hxB)
      (eqSbTm (ssbEqUpdate q₁ hxΓ hA) h₂ (ssbUpdate h₀ hxΓ hA))
  have qb : Γ ⊢ B[a'] ＝ B'[a'] ⦂ l' :=
    castTyEq (ssb_conc x a' B hxB) (ssb_conc x a' B' hxB')
      (sbDeriv (ssbUpdate h₁ hxΓ hA) q₀)
  exact .trans qa qb

/-- The last three premises are helpers. -/
theorem concEqTyInf {l l' : Lvl} {Γ : Cx} {A : Ty0} {a a' : Tm0} (B B' : Ty 1)
    (S : Fset) (q₀ : ∀ x, x # S → (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ＝ B'[x] ⦂ l')
    (q₁ : Γ ⊢ a ＝ a' ∶ A ⦂ l) (h₀ : Γ ⊢ a ∶ A ⦂ l) (h₁ : Γ ⊢ a' ∶ A ⦂ l)
    (h₂ : ∀ x, x # S → (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l') : Γ ⊢ B[a] ＝ B'[a'] ⦂ l' := by
  obtain ⟨x, hx⟩ := fresh (S, (B, B'))
  have hxS : x # S := notMem_union_left hx
  exact concEqTy B B' x (q₀ x hxS) q₁ (notMem_union_right hx) h₀ h₁ (h₂ x hxS)

/-- The last six premises are helpers. -/
theorem concEqTy₂ {l l' l'' : Lvl} {Γ : Cx} {A B : Ty0} {a a' b b' : Tm0}
    (C C' : Ty 2) (x y : Atom)
    (q₀ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢ C[x][y] ＝ C'[x][y] ⦂ l'')
    (q₁ : Γ ⊢ a ＝ a' ∶ A ⦂ l) (q₂ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B ⦂ l')
    (q₃ : Γ ⊢ b ＝ b' ∶ (x ≔ a) * B ⦂ l') (q₄ : x # (C, C')) (q₅ : y # (C, C'))
    (h₀ : Γ ⊢ a ∶ A ⦂ l) (h₁ : Γ ⊢ a' ∶ A ⦂ l) (h₂ : Γ ⊢ b ∶ (x ≔ a) * B ⦂ l')
    (h₃ : Γ ⊢ b' ∶ (x ≔ a') * B ⦂ l')
    (h₄ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢ C[x][y] ⦂ l'')
    (_h₅ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢ C'[x][y] ⦂ l'') :
    Γ ⊢ C[a][b] ＝ C'[a'][b'] ⦂ l'' := by
  have hxC : x # C := notMem_union_left q₄
  have hxC' : x # C' := notMem_union_right q₄
  have hyC : y # C := notMem_union_left q₅
  have hyC' : y # C' := notMem_union_right q₅
  obtain ⟨hyΓx, _, _⟩ := snocOkInv (derivOk q₀)
  have hyx : y # x := notMem_union_right hyΓx
  have qa : Γ ⊢ C[a][b] ＝ C[a'][b'] ⦂ l'' :=
    castTyEq (ssb_conc₂ x y a b C hxC (NotMem.union hyC hyx))
      (ssb_conc₂ x y a' b' C hxC (NotMem.union hyC hyx))
      (eqSbTm (ssbEqUpdate₂ q₁ q₂ q₃ hyΓx) h₄ (ssbUpdate₂ h₀ q₂ h₂ hyΓx))
  have qb : Γ ⊢ C[a'][b'] ＝ C'[a'][b'] ⦂ l'' :=
    castTyEq (ssb_conc₂ x y a' b' C hxC (NotMem.union hyC hyx))
      (ssb_conc₂ x y a' b' C' hxC' (NotMem.union hyC' hyx))
      (sbDeriv (ssbUpdate₂ h₁ q₂ h₃ hyΓx) q₀)
  exact .trans qa qb

/-- The last seven premises are helpers. -/
theorem concEqTy₂Inf {l l' l'' : Lvl} {Γ : Cx} {A : Ty0} {a a' b b' : Tm0} (B : Ty 1)
    (C C' : Ty 2) (S : Fset)
    (q₀ : ∀ x y, x # y # S →
      (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B[x] ⦂ l') ⊢ C[x][y] ＝ C'[x][y] ⦂ l'')
    (q₁ : Γ ⊢ a ＝ a' ∶ A ⦂ l) (q₂ : Γ ⊢ b ＝ b' ∶ B[a] ⦂ l')
    (h₀ : Γ ⊢ a ∶ A ⦂ l) (h₁ : Γ ⊢ a' ∶ A ⦂ l) (h₂ : Γ ⊢ b ∶ B[a] ⦂ l')
    (h₃ : Γ ⊢ b' ∶ B[a'] ⦂ l')
    (h₄ : ∀ x, x # S → (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l')
    (h₅ : ∀ x y, x # y # S → (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B[x] ⦂ l') ⊢ C[x][y] ⦂ l'')
    (h₆ : ∀ x y, x # y # S → (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B[x] ⦂ l') ⊢ C'[x][y] ⦂ l'') :
    Γ ⊢ C[a][b] ＝ C'[a'][b'] ⦂ l'' := by
  obtain ⟨y, hy⟩ := fresh (S, (C, C'))
  have hyS : y # S := notMem_union_left hy
  obtain ⟨x, hx⟩ := fresh (y, S, B, (C, C'))
  have hxy : x # y := notMem_union_left hx
  have hxS : x # S := notMem_union_left (notMem_union_right hx)
  have hxB : x # B := notMem_union_left (notMem_union_right (notMem_union_right hx))
  have hfr : x # y # S := Fresh₂.intro hyS hxS hxy
  exact concEqTy₂ (B := B[x]) C C' x y (q₀ x y hfr) q₁ (h₄ x hxS)
    (castEq rfl rfl (ssb_conc x a B hxB).symm q₂)
    (notMem_union_right (notMem_union_right (notMem_union_right hx)))
    (notMem_union_right hy) h₀ h₁
    (castTm rfl (ssb_conc x a B hxB).symm h₂)
    (castTm rfl (ssb_conc x a' B hxB).symm h₃)
    (h₅ x y hfr) (h₆ x y hfr)

/-! ## Reflexivity inversion

The Reflexivity rule says that `Γ ⊢ a ∶ A` implies `Γ ⊢ a ＝ a ∶ A`.  The converse,
which because of conversion symmetry/transitivity is equivalent to proving that
`Γ ⊢ a ＝ a' ∶ A` implies `Γ ⊢ a ∶ A`, is proved simultaneously with the statement
that `Γ ⊢ a ＝ a' ∶ A` also implies `Γ ⊢ a' ∶ A`.

Agda writes the two as a mutually recursive pair `⊢ty₁`/`⊢ty₂`.  Lean's `Deriv.rec`
takes a single motive, so the pair becomes the conjunction `tyBothGoal`, which is
vacuously true on typing judgements; `derivTy₁`/`derivTy₂` are its projections. -/

/-- The statement proved by induction for `derivTy₁`/`derivTy₂`: Agda's mutually
recursive pair `⊢ty₁`/`⊢ty₂`, packaged as one conjunction and made total on `Jg`. -/
private def tyBothGoal (Γ : Cx) : Jg → Prop
  | .ty _ _ _ => True
  | .eq a a' A l => (Γ ⊢ a ∶ A ⦂ l) ∧ (Γ ⊢ a' ∶ A ⦂ l)

/-- The induction behind `derivTy₁`/`derivTy₂`; see `tyBothGoal`. -/
private theorem tyBoth {Γ : Cx} {J : Jg} (q : Γ ⊢ J) : tyBothGoal Γ J := by
  induction q using Deriv.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc => trivial
  | conv => trivial
  | var => trivial
  | univ => trivial
  | pi => trivial
  | lam => trivial
  | app => trivial
  | idF => trivial
  | reflI => trivial
  | j => trivial
  | nat => trivial
  | zero => trivial
  | succ => trivial
  | nrec => trivial
  | refl q _ => exact ⟨q, q⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₀ ih₁ => exact ⟨ih₀.1, ih₁.2⟩
  | eqConv _ q₁ ih₀ _ => exact ⟨.conv ih₀.1 q₁, .conv ih₀.2 q₁⟩
  | @piCong Γ l l' A A' B B' S q₀ q₁ h ih₀ ih₁ _ =>
      exact ⟨.pi S ih₀.1 (fun x hx => (ih₁ x hx).1),
        .pi S ih₀.2 (fun x hx => snocEqDeriv (.symm q₀) (ih₁ x hx).2 ih₀.2)⟩
  | @lamCong Γ l l' A A' B b b' S q₀ q₁ h₀ h₁ ih₀ ih₁ _ _ =>
      have qq : Γ ⊢ 𝛌 A' b' ∶ 𝚷 l l' A' B ⦂ max l l' :=
        .lam S (fun x hx => snocEqDeriv (.symm q₀) (ih₁ x hx).2 ih₀.2) ih₀.2
          (fun x hx => snocEqDeriv (.symm q₀) (h₁ x hx) ih₀.2)
      have qq' : Γ ⊢ 𝚷 l l' A' B ＝ 𝚷 l l' A B ⦂ max l l' :=
        .piCong S (.symm q₀)
          (fun x hx => snocEqDeriv (.symm q₀) (.refl (h₁ x hx)) ih₀.2) ih₀.2
      exact ⟨.lam S (fun x hx => (ih₁ x hx).1) ih₀.1 h₁, .conv qq qq'⟩
  | @appCong Γ l l' A A' B B' a a' b b' S q₀ q₁ q₂ q₃ h₀ h₁ ih₀ ih₁ ih₂ ih₃ _ _ =>
      have qq : Γ ⊢ b' ∙[ A', B' ] a' ∶ B'[a'] ⦂ l' :=
        .app S (.conv ih₂.2 (.piCong S q₀ q₁ h₀)) (.conv ih₃.2 q₀)
          (fun x hx => snocEqDeriv (.symm q₀) (ih₁ x hx).2 ih₀.2) ih₀.2
      have qq' : Γ ⊢ B'[a'] ＝ B[a] ⦂ l' :=
        .symm (concEqTyInf B B' S q₁ q₃ ih₃.1 ih₃.2 h₁)
      exact ⟨.app S ih₂.1 ih₃.1 h₁ h₀, .conv qq qq'⟩
  | idCong q₀ _ _ ih₀ ih₁ ih₂ =>
      exact ⟨.idF ih₁.1 ih₂.1 ih₀.1, .idF (.conv ih₁.2 q₀) (.conv ih₂.2 q₀) ih₀.2⟩
  | reflCong q h ih₀ _ =>
      exact ⟨.reflI ih₀.1 h,
        .conv (.reflI ih₀.2 h) (.idCong (.refl h) (.symm q) (.symm q))⟩
  | @jCong Γ l l' A C C' a a' b b' c c' ee ee' S q₀ q₁ q₂ q₃ q₄ h₀ h₁
      ih₀ ih₁ ih₂ ih₃ ih₄ _ _ =>
      refine ⟨.j S (fun x y hf => (ih₀ x y hf).1) ih₁.1 ih₂.1 ih₃.1 ih₄.1 h₀ h₁, ?_⟩
      have hxΓ : ∀ x, x # S → x # Γ := fun x hx => (snocOkInv (derivOk (h₁ x hx))).1
      have hxa : ∀ x, x # S → x # a :=
        fun x hx => notMem_union_left (derivFresh q₁ (hxΓ x hx))
      have hxA : ∀ x, x # S → x # A := fun x hx =>
        notMem_union_right (notMem_union_right (derivFresh q₁ (hxΓ x hx)))
      have eqI : ∀ x, x # S → ∀ d : Tm0,
          (x ≔ d) * (𝐈𝐝 A a (𝐯x) : Ty0) = 𝐈𝐝 A a d := by
        intro x hx d
        rw [sbId, ssbFresh x d A (hxA x hx), ssbFresh x d a (hxa x hx), sbAtom,
          Sb.single_eq]
      have r₁ : ∀ x, x # S →
          (Γ ⨟ x ∶ A ⦂ l) ⊢ 𝐈𝐝 A a' (𝐯x) ＝ 𝐈𝐝 A a (𝐯x) ⦂ l := fun x hx =>
        .idCong (.refl (wkDeriv (wkProj h₀ (hxΓ x hx)) h₀))
          (.symm (wkDeriv (wkProj h₀ (hxΓ x hx)) q₁))
          (.refl (.var (derivOk (h₁ x hx)) .new))
      have r₂ : ∀ x, x # S → (Γ ⨟ x ∶ A ⦂ l) ⊢ 𝐈𝐝 A a' (𝐯x) ⦂ l := fun x hx =>
        .idF (wkDeriv (wkProj h₀ (hxΓ x hx)) ih₁.2) (.var (derivOk (h₁ x hx)) .new)
          (wkDeriv (wkProj h₀ (hxΓ x hx)) h₀)
      have qc : Γ ⊢ C[a][(𝐫𝐞𝐟𝐥 a : Tm0)] ＝ C'[a'][(𝐫𝐞𝐟𝐥 a' : Tm0)] ⦂ l' := by
        obtain ⟨y, hy⟩ := fresh (S, (C, C'))
        have hyS : y # S := notMem_union_left hy
        obtain ⟨x, hx⟩ := fresh (y, S, (C, C'))
        have hxy : x # y := notMem_union_left hx
        have hxS : x # S := notMem_union_left (notMem_union_right hx)
        have hfr : x # y # S := Fresh₂.intro hyS hxS hxy
        exact concEqTy₂ C C' x y (q₀ x y hfr) q₁ (h₁ x hxS)
          (castEq rfl rfl (eqI x hxS a).symm (.reflCong q₁ h₀))
          (notMem_union_right (notMem_union_right hx)) (notMem_union_right hy)
          ih₁.1 ih₁.2
          (castTm rfl (eqI x hxS a).symm (.reflI ih₁.1 h₀))
          (castTm rfl (eqI x hxS a').symm
            (.conv (.reflI ih₁.2 h₀) (.idCong (.refl h₀) (.symm q₁) (.refl ih₁.2))))
          (ih₀ x y hfr).1 (ih₀ x y hfr).2
      have qj : Γ ⊢ 𝐉 C' a' b' c' ee' ∶ C'[b'][ee'] ⦂ l' := by
        refine .j S (fun x y hf => ?_) (.conv ih₁.2 (.refl h₀))
          (.conv ih₂.2 (.refl h₀)) (.conv ih₃.2 qc)
          (.conv ih₄.2 (.idCong (.refl h₀) q₁ q₂)) h₀ r₂
        obtain ⟨_, hxS, _⟩ := Fresh₂.inv hf
        exact snocEqDeriv (r₁ x hxS) (ih₀ x y hf).2 (r₂ x hxS)
      have qe : Γ ⊢ C'[b'][ee'] ＝ C[b][ee] ⦂ l' := by
        obtain ⟨y, hy⟩ := fresh (S, (C, C'))
        have hyS : y # S := notMem_union_left hy
        obtain ⟨x, hx⟩ := fresh (y, S, (C, C'))
        have hxy : x # y := notMem_union_left hx
        have hxS : x # S := notMem_union_left (notMem_union_right hx)
        have hfr : x # y # S := Fresh₂.intro hyS hxS hxy
        exact .symm (concEqTy₂ C C' x y (q₀ x y hfr) q₂ (h₁ x hxS)
          (castEq rfl rfl (eqI x hxS b).symm q₄)
          (notMem_union_right (notMem_union_right hx)) (notMem_union_right hy)
          ih₂.1 ih₂.2
          (castTm rfl (eqI x hxS b).symm ih₄.1)
          (castTm rfl (eqI x hxS b').symm
            (.conv ih₄.2 (.idCong (.refl h₀) (.refl ih₁.1) q₂)))
          (ih₀ x y hfr).1 (ih₀ x y hfr).2)
      exact .conv qj qe
  | succCong _ ih => exact ⟨.succ ih.1, .succ ih.2⟩
  | @nrecCong Γ l C C' c₀ c₀' a a' cs cs' S q₀ q₁ q₂ q₃ h ih₀ ih₁ ih₂ ih₃ _ =>
      refine ⟨.nrec S ih₁.1 (fun x y hf => (ih₂ x y hf).1) ih₃.1 h, ?_⟩
      have qa : Γ ⊢ C[a] ＝ C'[a'] ⦂ l := concEqTyInf C C' S q₀ q₃ ih₃.1 ih₃.2 h
      have qz : Γ ⊢ C[(𝐳𝐞𝐫𝐨 : Tm0)] ＝ C'[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l :=
        concEqTyInf C C' S q₀ (.refl (.zero (derivOk q₃))) (.zero (derivOk q₃))
          (.zero (derivOk q₃)) h
      have qn : Γ ⊢ 𝐧𝐫𝐞𝐜 C' c₀' cs' a' ∶ C'[a'] ⦂ l := by
        refine .nrec S (.conv ih₁.2 qz) (fun x y hf => ?_) ih₃.2
          (fun x hx => (ih₀ x hx).2)
        obtain ⟨hyS, hxS, _⟩ := Fresh₂.inv hf
        have hxΓ : x # Γ := (snocOkInv (derivOk (h x hxS))).1
        have hyΓx : y # (Γ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) :=
          (snocOkInv (derivOk (q₂ x y hf))).1
        have hyΓ : y # Γ := notMem_union_left hyΓx
        have hyC : y # C := subset_notMem (conc_supp C (𝐳𝐞𝐫𝐨 : Tm0))
          (notMem_union_right (notMem_union_right (derivFresh q₁ hyΓ)))
        have hyC' : y # C' := subset_notMem (conc_supp C' (𝐯x : Tm0))
          (notMem_union_left (notMem_union_right (derivFresh (q₀ x hxS) hyΓx)))
        have hsx : (Γ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) ⊢ 𝐬𝐮𝐜𝐜 (𝐯x) ∶ 𝐍𝐚𝐭 ⦂ 0 :=
          .succ (.var (derivOk (q₀ x hxS)) .new)
        have hwk : (Γ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) ▷ Γ :=
          wkProj (Deriv.nat (derivOk q₁)) hxΓ
        have hcc : (Γ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) ⊢
            C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] ＝ C'[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] ⦂ l :=
          concEqTy C C' y (wkSnocDeriv (q₀ y hyS) hwk hyΓx) (.refl hsx)
            (NotMem.union hyC hyC') hsx hsx (wkSnocDeriv (h y hyS) hwk hyΓx)
        exact snocEqDeriv (.symm (q₀ x hxS))
          (.conv (ih₂ x y hf).2 (wkDeriv (wkProj (h x hxS) hyΓx) hcc))
          (ih₀ x hxS).2
      exact .conv qn (.symm qa)
  | @piBeta Γ l l' A a B b S q₀ q₁ h₀ h₁ _ _ _ _ =>
      exact ⟨.app S (.lam S q₀ h₀ h₁) q₁ h₁ h₀, concTmInf B b S q₀ q₁⟩
  | idBeta S q₀ q₁ q₂ h₀ h₁ _ _ _ _ _ =>
      exact ⟨.j S q₀ q₁ q₁ q₂ (.reflI q₁ h₀) h₀ h₁, q₂⟩
  | natBeta₀ S q₀ q₁ h _ _ _ =>
      exact ⟨.nrec S q₀ q₁ (.zero (derivOk q₀)) h, q₀⟩
  | @natBetaS Γ l C c₀ a cs S q₀ q₁ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      clear ih₀ ih₁ ih₂ ih₃
      refine ⟨.nrec S q₀ q₁ (.succ q₂) h, ?_⟩
      obtain ⟨y, hy⟩ := fresh (S, cs)
      have hyS : y # S := notMem_union_left hy
      have hycs : y # cs := notMem_union_right hy
      obtain ⟨x, hx⟩ := fresh (y, S, C, cs)
      have hxy : x # y := notMem_union_left hx
      have hxS : x # S := notMem_union_left (notMem_union_right hx)
      have hxC : x # C :=
        notMem_union_left (notMem_union_right (notMem_union_right hx))
      have hxcs : x # cs :=
        notMem_union_right (notMem_union_right (notMem_union_right hx))
      have hfr : x # y # S := Fresh₂.intro hyS hxS hxy
      have hxΓ : x # Γ := (snocOkInv (derivOk (h x hxS))).1
      have hyΓx : y # (Γ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0) :=
        (snocOkInv (derivOk (q₁ x y hfr))).1
      have hyΓ : y # Γ := notMem_union_left hyΓx
      have hyx : y ≠ x := Fset.ne_of_notMem_single (notMem_union_right hyΓx)
      have hyC : y # C := subset_notMem (conc_supp C (𝐳𝐞𝐫𝐨 : Tm0))
        (notMem_union_right (derivFresh q₀ hyΓ))
      have r : Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ cs a ∶ (x ≔ a) * (C[x] : Ty0) ⦂ l :=
        castTm rfl (ssb_conc x a C hxC).symm (.nrec S q₀ q₁ q₂ h)
      have s : Γ ⊢ˢ ((x ≔ a) ∘/ y ≔ (𝐧𝐫𝐞𝐜 C c₀ cs a : Tm0)) ∶
          (Γ ⨟ x ∶ (𝐍𝐚𝐭 : Ty0) ⦂ 0 ⨟ y ∶ C[x] ⦂ l) :=
        sbUpdate (ssbUpdate q₂ hxΓ (.nat (derivOk q₀))) r hyΓx (h x hxS)
      have e : ((x ≔ a) ∘/ y ≔ (𝐧𝐫𝐞𝐜 C c₀ cs a : Tm0)) *
          (C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] : Ty0) = C[(𝐬𝐮𝐜𝐜 a : Tm0)] := by
        rw [sb_conc, updateFresh (x ≔ a) y (𝐧𝐫𝐞𝐜 C c₀ cs a) C hyC,
          ssbFresh x a C hxC, sbSucc, sbAtom, Sb.update_neq _ _ hyx, Sb.single_eq]
      exact castTm
        (ssb_conc₂ x y a (𝐧𝐫𝐞𝐜 C c₀ cs a) cs hxcs
          (NotMem.union hycs (notMem_union_right hyΓx)))
        e (sbDeriv s (q₁ x y hfr))
  | piEta _ q₀ q₁ _ _ _ _ _ _ => exact ⟨q₀, q₁⟩

theorem derivTy₁ {l : Lvl} {Γ : Cx} {A : Ty0} {a a' : Tm0}
    (q : Γ ⊢ a ＝ a' ∶ A ⦂ l) : Γ ⊢ a ∶ A ⦂ l := (tyBoth q).1

theorem derivTy₂ {l : Lvl} {Γ : Cx} {A : Ty0} {a a' : Tm0}
    (q : Γ ⊢ a ＝ a' ∶ A ⦂ l) : Γ ⊢ a' ∶ A ⦂ l := (tyBoth q).2

/-! ## Reflexivity inversion for substitutions -/

theorem sbTy₁ {Γ Γ' : Cx} {σ σ' : Sb sig} (p : Γ ⊢ˢ σ ＝ σ' ∶ Γ') : Γ ⊢ˢ σ ∶ Γ' := by
  induction p with
  | nil q => exact .nil q
  | snoc _ q₁ q₂ q₃ ih => exact .snoc ih q₁ (derivTy₁ q₂) q₃

theorem sbTy₂ {Γ Γ' : Cx} {σ σ' : Sb sig} (p : Γ ⊢ˢ σ ＝ σ' ∶ Γ') : Γ ⊢ˢ σ' ∶ Γ' := by
  induction p with
  | nil q => exact .nil q
  | snoc q₀ q₁ q₂ q₃ ih =>
      exact .snoc ih q₁ (.conv (derivTy₂ q₂) (eqSbTm q₀ q₁ (sbTy₁ q₀))) q₃

/-! ## Congruence property of substitution -/

theorem congSbTm {l : Lvl} {σ σ' : Sb sig} {Γ Γ' : Cx} {A : Ty0} {a a' : Tm0}
    (q : Γ' ⊢ˢ σ ＝ σ' ∶ Γ) (q' : Γ ⊢ a ＝ a' ∶ A ⦂ l) :
    Γ' ⊢ σ * a ＝ σ' * a' ∶ σ * A ⦂ l :=
  .trans (sbDeriv (sbTy₁ q) q') (eqSbTm q (derivTy₂ q') (sbTy₁ q))

/-! ## Substitution properties of concretion, continued -/

theorem concTy {l l' : Lvl} {Γ : Cx} {A : Ty0} {a : Tm0} (B : Ty 1) (x : Atom)
    (q₀ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l') (q₁ : Γ ⊢ a ∶ A ⦂ l) (q₂ : x # B) :
    Γ ⊢ B[a] ⦂ l' :=
  concTm (𝐔 l') B x q₀ q₁ (NotMem.union (freshU x l') q₂)

theorem concTyInf {l l' : Lvl} {Γ : Cx} {A : Ty0} {a : Tm0} (B : Ty 1) (S : Fset)
    (q₀ : ∀ x, x # S → (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l') (q₁ : Γ ⊢ a ∶ A ⦂ l) :
    Γ ⊢ B[a] ⦂ l' := concTmInf (𝐔 l') B S q₀ q₁

theorem concTy₂ {l l' l'' : Lvl} {Γ : Cx} {A B : Ty0} {a b : Tm0} (C : Ty 2)
    (x y : Atom) (q₀ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢ C[x][y] ⦂ l'')
    (q₁ : Γ ⊢ a ∶ A ⦂ l) (q₂ : Γ ⊢ b ∶ (x ≔ a) * B ⦂ l') (q₃ : x # C) (q₄ : y # C) :
    Γ ⊢ C[a][b] ⦂ l'' := by
  obtain ⟨hyΓx, hB, _⟩ := snocOkInv (derivOk q₀)
  exact castIsTy
    (ssb_conc₂ x y a b C q₃ (NotMem.union q₄ (notMem_union_right hyΓx)))
    (sbDeriv (ssbUpdate₂ q₁ hB q₂ hyΓx) q₀)

/-! ## Well-formed contexts contain well-formed types -/

theorem okVarTy {l : Lvl} {Γ : Cx} {A : Ty0} {x : Atom} (p : Ok Γ)
    (q : (x, A, l) isIn Γ) : Γ ⊢ A ⦂ l := by
  revert p q
  induction Γ with
  | nil => intro _ q; cases q
  | snoc Γ' y B l' ih =>
      intro p q
      cases q with
      | new =>
          cases p with
          | snoc q₀ q₁ _ => exact wkDeriv (wkProj q₀ q₁) q₀
      | old q' =>
          cases p with
          | snoc q₀ q₁ hh => exact wkDeriv (wkProj q₀ q₁) (ih hh q')

/-! ## Well-typed terms have well-formed types -/

/-- The statement proved by induction for `derivTyOfTm`: Agda's `⊢∶ty` only has
clauses for the typing constructors, because its result type forces the judgement to
be of the form `a ∶ A ⦂ l`; Lean's `Deriv.rec` demands all thirty cases. -/
private def tyOfTmGoal (Γ : Cx) : Jg → Prop
  | .ty _ A l => Γ ⊢ A ⦂ l
  | .eq _ _ _ _ => True

/-- The induction behind `derivTyOfTm`; see `tyOfTmGoal`. -/
private theorem tyOfTmAux {Γ : Cx} {J : Jg} (q : Γ ⊢ J) : tyOfTmGoal Γ J := by
  induction q using Deriv.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc => trivial
  | conv _ q₁ => exact derivTy₂ q₁
  | var q₀ q₁ => exact okVarTy q₀ q₁
  | univ q => exact .univ q
  | pi _ q₀ => exact .univ (derivOk q₀)
  | lam S _ h₀ h₁ => exact .pi S h₀ h₁
  | @app Γ l l' A B a b S _ q₁ q₂ => exact concTyInf B S q₂ q₁
  | idF _ _ _ _ _ ih₂ => exact ih₂
  | reflI q h => exact .idF q q h
  | @j Γ l l' A C a b c ee S q₀ q₁ q₂ q₃ q₄ h₀ h₁ =>
      obtain ⟨y, hy⟩ := fresh (S, C)
      have hyS : y # S := notMem_union_left hy
      have hyC : y # C := notMem_union_right hy
      obtain ⟨x, hx⟩ := fresh (y, S, C)
      have hxy : x # y := notMem_union_left hx
      have hxS : x # S := notMem_union_left (notMem_union_right hx)
      have hxC : x # C := notMem_union_right (notMem_union_right hx)
      have hfr : x # y # S := Fresh₂.intro hyS hxS hxy
      have hxΓ : x # Γ := (snocOkInv (derivOk (h₁ x hxS))).1
      have hfrq := derivFresh q₁ hxΓ
      have hxa : x # a := notMem_union_left hfrq
      have hxA : x # A := notMem_union_right hfrq
      have eqI : (x ≔ b) * (𝐈𝐝 A a (𝐯x) : Ty0) = 𝐈𝐝 A a b := by
        rw [sbId, ssbFresh x b A hxA, ssbFresh x b a hxa, sbAtom, Sb.single_eq]
      exact concTy₂ C x y (q₀ x y hfr) q₂ (castTm rfl eqI.symm q₄) hxC hyC
  | nat q => exact .univ q
  | zero q => exact .nat q
  | succ _ ih => exact ih
  | @nrec Γ l C c₀ a cs S _ _ q₂ h => exact concTyInf C S h q₂
  | refl => trivial
  | symm => trivial
  | trans => trivial
  | eqConv => trivial
  | piCong => trivial
  | lamCong => trivial
  | appCong => trivial
  | idCong => trivial
  | reflCong => trivial
  | jCong => trivial
  | succCong => trivial
  | nrecCong => trivial
  | piBeta => trivial
  | idBeta => trivial
  | natBeta₀ => trivial
  | natBetaS => trivial
  | piEta => trivial

theorem derivTyOfTm {l : Lvl} {Γ : Cx} {A : Ty0} {a : Tm0} (q : Γ ⊢ a ∶ A ⦂ l) :
    Γ ⊢ A ⦂ l := tyOfTmAux q

/-! ## Properties of context conversion

Reflexivity (`cxRefl`) was proved above. -/

theorem cxSymm {Γ Γ' : Cx} (p : ⊢ Γ ＝ Γ') : ⊢ Γ' ＝ Γ := by
  induction p with
  | nil => exact .nil
  | @snoc l Γ₁ Γ₂ A A' x q₀ q₁ q₂ h₀ h₁ ih =>
      exact .snoc ih (eqDeriv (.symm q₁) ih)
        (NotMem.union (notMem_union_right q₂) (notMem_union_left q₂)) h₁ h₀

theorem cxTrans {Γ Γ' Γ'' : Cx} (p : ⊢ Γ ＝ Γ') (p' : ⊢ Γ' ＝ Γ'') : ⊢ Γ ＝ Γ'' := by
  revert Γ''
  induction p with
  | nil => intro Γ'' p'; cases p'; exact .nil
  | @snoc l Γ₁ Γ₂ A A' x q₀ q₁ q₂ h₀ h₁ ih =>
      intro Γ'' p'
      cases p' with
      | snoc q₀' q₁' q₂' h₀' h₁' =>
          exact .snoc (ih q₀') (.trans q₁ (eqDeriv q₁' q₀))
            (NotMem.union (notMem_union_left q₂) (notMem_union_right q₂')) h₀ h₁'

end MLTT

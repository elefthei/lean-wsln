import MLTT.Admissible

/-!
# "Exists fresh" style rules

Port of `agda-code/agda/MLTT/ExistsFresh.agda`.

The cofinite rules of `MLTT/Cofinite.lean` quantify over *every* atom outside a finite
exclusion set and carry redundant helper premises.  Each theorem below takes instead
one chosen atom (two for the doubly bound motives), a derivation opened at that atom,
and explicit freshness of the atom for the binder bodies.  The cofinite derivation is
rebuilt by choosing `S := dom Γ` and renaming the given premise to every fresh atom
with `rnSnoc`/`rnSnoc₂`, transporting along the WSLN concretion/substitution equations.
-/

namespace MLTT

open WSLN
open Fset

/-! ## Plumbing with no Agda counterpart -/

/-- Agda transports the type of the last context entry inside the same `subst` that
transports the judgement; in Lean the two are separate casts. -/
private theorem castCxSnoc {Γ : Cx} {x : Atom} {l : Lvl} {A A' : Ty0} {J : Jg}
    (e : A = A') (d : (Γ ⨟ x ∶ A ⦂ l) ⊢ J) : (Γ ⨟ x ∶ A' ⦂ l) ⊢ J := by
  subst e; exact d

/-! ## Type formation and typing -/

theorem piEF {Γ : Cx} {l l' : Lvl} {A : Ty0} {B : Ty 1} {x : Atom} (q₀ : Γ ⊢ A ⦂ l)
    (q₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l') (q₂ : x # B) : Γ ⊢ 𝚷 l l' A B ⦂ max l l' :=
  .pi (dom Γ) q₀ fun y hy => castIsTy (ssb_conc x (𝐯y) B q₂) (rnSnoc q₁ hy)

theorem lamEF {l l' : Lvl} {Γ : Cx} {A : Ty0} {B : Ty 1} {b : Tm 1} {x : Atom}
    (q : (Γ ⨟ x ∶ A ⦂ l) ⊢ b[x] ∶ B[x] ⦂ l') (hx : x # (B, b)) :
    Γ ⊢ 𝛌 A b ∶ 𝚷 l l' A B ⦂ max l l' := by
  have hxB : x # B := notMem_union_left hx
  have hxb : x # b := notMem_union_right hx
  obtain ⟨_, hA, _⟩ := snocOkInv (derivOk q)
  exact .lam (dom Γ)
    (fun y hy => castTm (ssb_conc x (𝐯y) b hxb) (ssb_conc x (𝐯y) B hxB) (rnSnoc q hy))
    hA
    (fun y hy => castIsTy (ssb_conc x (𝐯y) B hxB) (rnSnoc (derivTyOfTm q) hy))

theorem appEF {l l' : Lvl} {Γ : Cx} {A : Ty0} {B : Ty 1} {a b : Tm0} {x : Atom}
    (q₀ : Γ ⊢ b ∶ 𝚷 l l' A B ⦂ max l l') (q₁ : Γ ⊢ a ∶ A ⦂ l)
    (q₂ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l') (q₃ : x # B) :
    Γ ⊢ b ∙[ A, B ] a ∶ B[a] ⦂ l' :=
  .app (dom Γ) q₀ q₁
    (fun y hy => castIsTy (ssb_conc x (𝐯y) B q₃) (rnSnoc q₂ hy)) (derivTyOfTm q₁)

theorem idFEF {l : Lvl} {Γ : Cx} {A a b : Tm0} (q₀ : Γ ⊢ a ∶ A ⦂ l)
    (q₁ : Γ ⊢ b ∶ A ⦂ l) : Γ ⊢ 𝐈𝐝 A a b ⦂ l := .idF q₀ q₁ (derivTyOfTm q₀)

theorem reflIEF {l : Lvl} {Γ : Cx} {A : Ty0} {a : Tm0} (q : Γ ⊢ a ∶ A ⦂ l) :
    Γ ⊢ 𝐫𝐞𝐟𝐥 a ∶ 𝐈𝐝 A a a ⦂ l := .reflI q (derivTyOfTm q)

theorem jEF {l l' : Lvl} {Γ : Cx} {A : Ty0} {C : Ty 2} {a b c e : Tm0} {x y : Atom}
    (q₀ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ 𝐈𝐝 A a (𝐯x) ⦂ l) ⊢ C[x][y] ⦂ l')
    (q₁ : Γ ⊢ a ∶ A ⦂ l) (q₂ : Γ ⊢ b ∶ A ⦂ l)
    (q₃ : Γ ⊢ c ∶ C[a][(𝐫𝐞𝐟𝐥 a : Tm0)] ⦂ l') (q₄ : Γ ⊢ e ∶ 𝐈𝐝 A a b ⦂ l)
    (q₅ : x # C) (q₆ : y # C) : Γ ⊢ 𝐉 C a b c e ∶ C[b][e] ⦂ l' := by
  obtain ⟨hyΓx, hI, hOk⟩ := snocOkInv (derivOk q₀)
  obtain ⟨hxΓ, hA, _⟩ := snocOkInv hOk
  have hyx : y # x := notMem_union_right hyΓx
  have hxA : x # A := notMem_union_left (derivFresh hA hxΓ)
  have hxa : x # a := notMem_union_left (derivFresh q₁ hxΓ)
  have eqI : ∀ d : Tm0, (x ≔ d) * (𝐈𝐝 A a (𝐯x) : Ty0) = 𝐈𝐝 A a d := by
    intro d
    rw [sbId, ssbFresh x d A hxA, ssbFresh x d a hxa, sbAtom, Sb.single_eq]
  refine .j (dom Γ) (fun x' y' hf => ?_) q₁ q₂ q₃ q₄ (derivTyOfTm q₁)
    (fun x' hx' => castIsTy (eqI (𝐯x')) (rnSnoc hI hx'))
  obtain ⟨hy'Γ, hx'Γ, hx'y'⟩ := Fresh₂.inv hf
  exact castCxSnoc (eqI (𝐯x'))
    (castIsTy (ssb_conc₂ x y (𝐯x') (𝐯y') C q₅ (NotMem.union q₆ hyx))
      (rnSnoc₂ q₀ hx'Γ (NotMem.union (fresh_symm hx'y') hy'Γ)))

theorem nrecEF {l : Lvl} {Γ : Cx} {C : Ty 1} {c₀ a : Tm0} {cs : Tm 2} {x y : Atom}
    (q₀ : Γ ⊢ c₀ ∶ C[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l)
    (q₁ : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C[x] ⦂ l) ⊢ cs[x][y] ∶ C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] ⦂ l)
    (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ⦂ 0) (q₃ : x # (C, cs)) (q₄ : y # cs) :
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ cs a ∶ C[a] ⦂ l := by
  have hxC : x # C := notMem_union_left q₃
  have hxcs : x # cs := notMem_union_right q₃
  obtain ⟨hyΓx, hCx, _⟩ := snocOkInv (derivOk q₁)
  have hyΓ : y # Γ := notMem_union_left hyΓx
  have hyx : y # x := notMem_union_right hyΓx
  have hyC : y # C := subset_notMem (conc_supp C (𝐳𝐞𝐫𝐨 : Tm0))
    (notMem_union_right (derivFresh q₀ hyΓ))
  have hyxne : y ≠ x := Fset.ne_of_notMem_single hyx
  have eqC : ∀ u v : Tm0,
      ((x ≔ u) ∘/ y ≔ v) * (C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] : Ty0) = C[(𝐬𝐮𝐜𝐜 u : Tm0)] := by
    intro u v
    rw [sb_conc, updateFresh (x ≔ u) y v C hyC, ssbFresh x u C hxC, sbSucc, sbAtom,
      Sb.update_neq _ _ hyxne, Sb.single_eq]
  refine .nrec (dom Γ) q₀ (fun x' y' hf => ?_) q₂
    (fun x' hx' => castIsTy (ssb_conc x (𝐯x') C hxC) (rnSnoc hCx hx'))
  obtain ⟨hy'Γ, hx'Γ, hx'y'⟩ := Fresh₂.inv hf
  exact castCxSnoc (ssb_conc x (𝐯x') C hxC)
    (castTm (ssb_conc₂ x y (𝐯x') (𝐯y') cs hxcs (NotMem.union q₄ hyx))
      (eqC (𝐯x') (𝐯y'))
      (rnSnoc₂ q₁ hx'Γ (NotMem.union (fresh_symm hx'y') hy'Γ)))

/-! ## Congruence rules -/

theorem piCongEF {l l' : Lvl} {Γ : Cx} {A A' : Ty0} {B B' : Ty 1} {x : Atom}
    (q₀ : Γ ⊢ A ＝ A' ⦂ l) (q₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ＝ B'[x] ⦂ l')
    (q₂ : x # (B, B')) : Γ ⊢ 𝚷 l l' A B ＝ 𝚷 l l' A' B' ⦂ max l l' := by
  have hxB : x # B := notMem_union_left q₂
  have hxB' : x # B' := notMem_union_right q₂
  exact .piCong (dom Γ) q₀
    (fun x' hx' => castTyEq (ssb_conc x (𝐯x') B hxB) (ssb_conc x (𝐯x') B' hxB')
      (rnSnoc q₁ hx'))
    (derivTy₁ q₀)

theorem lamCongEF {l l' : Lvl} {Γ : Cx} {A A' : Ty0} {B : Ty 1} {b b' : Tm 1}
    {x : Atom} (q₀ : Γ ⊢ A ＝ A' ⦂ l)
    (q₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ b[x] ＝ b'[x] ∶ B[x] ⦂ l') (q₂ : x # (B, b, b')) :
    Γ ⊢ 𝛌 A b ＝ 𝛌 A' b' ∶ 𝚷 l l' A B ⦂ max l l' := by
  have hxB : x # B := notMem_union_left q₂
  have hxb : x # b := notMem_union_left (notMem_union_right q₂)
  have hxb' : x # b' := notMem_union_right (notMem_union_right q₂)
  exact .lamCong (dom Γ) q₀
    (fun x' hx' => castEq (ssb_conc x (𝐯x') b hxb) (ssb_conc x (𝐯x') b' hxb')
      (ssb_conc x (𝐯x') B hxB) (rnSnoc q₁ hx'))
    (derivTy₁ q₀)
    (fun x' hx' => castIsTy (ssb_conc x (𝐯x') B hxB)
      (rnSnoc (derivTyOfTm (derivTy₁ q₁)) hx'))

theorem appCongEF {l l' : Lvl} {Γ : Cx} {A A' : Ty0} {B B' : Ty 1} {a a' b b' : Tm0}
    {x : Atom} (q₀ : Γ ⊢ A ＝ A' ⦂ l)
    (q₁ : (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ＝ B'[x] ⦂ l')
    (q₂ : Γ ⊢ b ＝ b' ∶ 𝚷 l l' A B ⦂ max l l') (q₃ : Γ ⊢ a ＝ a' ∶ A ⦂ l)
    (q₄ : x # (B, B')) : Γ ⊢ b ∙[ A, B ] a ＝ b' ∙[ A', B' ] a' ∶ B[a] ⦂ l' := by
  have hxB : x # B := notMem_union_left q₄
  have hxB' : x # B' := notMem_union_right q₄
  exact .appCong (dom Γ) q₀
    (fun x' hx' => castTyEq (ssb_conc x (𝐯x') B hxB) (ssb_conc x (𝐯x') B' hxB')
      (rnSnoc q₁ hx'))
    q₂ q₃ (derivTy₁ q₀)
    (fun x' hx' => castIsTy (ssb_conc x (𝐯x') B hxB) (rnSnoc (derivTy₁ q₁) hx'))

theorem reflCongEF {l : Lvl} {Γ : Cx} {A : Ty0} {a a' : Tm0}
    (q : Γ ⊢ a ＝ a' ∶ A ⦂ l) : Γ ⊢ 𝐫𝐞𝐟𝐥 a ＝ 𝐫𝐞𝐟𝐥 a' ∶ 𝐈𝐝 A a a ⦂ l :=
  .reflCong q (derivTyOfTm (derivTy₁ q))

theorem jCongEF {l l' : Lvl} {Γ : Cx} {A : Ty0} {C C' : Ty 2}
    {a a' b b' c c' e e' : Tm0} {x y : Atom}
    (q₀ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ 𝐈𝐝 A a (𝐯x) ⦂ l) ⊢ C[x][y] ＝ C'[x][y] ⦂ l')
    (q₁ : Γ ⊢ a ＝ a' ∶ A ⦂ l) (q₂ : Γ ⊢ b ＝ b' ∶ A ⦂ l)
    (q₃ : Γ ⊢ c ＝ c' ∶ C[a][(𝐫𝐞𝐟𝐥 a : Tm0)] ⦂ l')
    (q₄ : Γ ⊢ e ＝ e' ∶ 𝐈𝐝 A a b ⦂ l) (q₅ : x # (C, C')) (q₆ : y # (C, C')) :
    Γ ⊢ 𝐉 C a b c e ＝ 𝐉 C' a' b' c' e' ∶ C[b][e] ⦂ l' := by
  have hxC : x # C := notMem_union_left q₅
  have hxC' : x # C' := notMem_union_right q₅
  have hyC : y # C := notMem_union_left q₆
  have hyC' : y # C' := notMem_union_right q₆
  obtain ⟨hyΓx, hI, hOk⟩ := snocOkInv (derivOk q₀)
  obtain ⟨hxΓ, hA, _⟩ := snocOkInv hOk
  have hyx : y # x := notMem_union_right hyΓx
  have hxA : x # A := notMem_union_left (derivFresh hA hxΓ)
  have hxa : x # a := notMem_union_left (derivFresh q₁ hxΓ)
  have eqI : ∀ d : Tm0, (x ≔ d) * (𝐈𝐝 A a (𝐯x) : Ty0) = 𝐈𝐝 A a d := by
    intro d
    rw [sbId, ssbFresh x d A hxA, ssbFresh x d a hxa, sbAtom, Sb.single_eq]
  refine .jCong (dom Γ) (fun x' y' hf => ?_) q₁ q₂ q₃ q₄ hA
    (fun x' hx' => castIsTy (eqI (𝐯x')) (rnSnoc hI hx'))
  obtain ⟨hy'Γ, hx'Γ, hx'y'⟩ := Fresh₂.inv hf
  exact castCxSnoc (eqI (𝐯x'))
    (castTyEq (ssb_conc₂ x y (𝐯x') (𝐯y') C hxC (NotMem.union hyC hyx))
      (ssb_conc₂ x y (𝐯x') (𝐯y') C' hxC' (NotMem.union hyC' hyx))
      (rnSnoc₂ q₀ hx'Γ (NotMem.union (fresh_symm hx'y') hy'Γ)))

theorem nrecCongEF {l : Lvl} {Γ : Cx} {C C' : Ty 1} {c₀ c₀' a a' : Tm0}
    {cs cs' : Tm 2} {x y : Atom}
    (q₀ : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0) ⊢ C[x] ＝ C'[x] ⦂ l)
    (q₁ : Γ ⊢ c₀ ＝ c₀' ∶ C[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l)
    (q₂ : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C[x] ⦂ l) ⊢
      cs[x][y] ＝ cs'[x][y] ∶ C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] ⦂ l)
    (q₃ : Γ ⊢ a ＝ a' ∶ 𝐍𝐚𝐭 ⦂ 0) (q₄ : x # (C, C', cs, cs')) (q₅ : y # (cs, cs')) :
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ cs a ＝ 𝐧𝐫𝐞𝐜 C' c₀' cs' a' ∶ C[a] ⦂ l := by
  have hxC : x # C := notMem_union_left q₄
  have hxC' : x # C' := notMem_union_left (notMem_union_right q₄)
  have hxcs : x # cs :=
    notMem_union_left (notMem_union_right (notMem_union_right q₄))
  have hxcs' : x # cs' :=
    notMem_union_right (notMem_union_right (notMem_union_right q₄))
  have hycs : y # cs := notMem_union_left q₅
  have hycs' : y # cs' := notMem_union_right q₅
  obtain ⟨hyΓx, hCx, _⟩ := snocOkInv (derivOk q₂)
  have hyΓ : y # Γ := notMem_union_left hyΓx
  have hyx : y # x := notMem_union_right hyΓx
  have hyC : y # C := subset_notMem (conc_supp C (𝐳𝐞𝐫𝐨 : Tm0))
    (notMem_union_right (notMem_union_right (derivFresh q₁ hyΓ)))
  have hyxne : y ≠ x := Fset.ne_of_notMem_single hyx
  have eqC : ∀ u v : Tm0,
      ((x ≔ u) ∘/ y ≔ v) * (C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] : Ty0) = C[(𝐬𝐮𝐜𝐜 u : Tm0)] := by
    intro u v
    rw [sb_conc, updateFresh (x ≔ u) y v C hyC, ssbFresh x u C hxC, sbSucc, sbAtom,
      Sb.update_neq _ _ hyxne, Sb.single_eq]
  refine .nrecCong (dom Γ)
    (fun x' hx' => castTyEq (ssb_conc x (𝐯x') C hxC) (ssb_conc x (𝐯x') C' hxC')
      (rnSnoc q₀ hx'))
    q₁ (fun x' y' hf => ?_) q₃
    (fun x' hx' => castIsTy (ssb_conc x (𝐯x') C hxC) (rnSnoc hCx hx'))
  obtain ⟨hy'Γ, hx'Γ, hx'y'⟩ := Fresh₂.inv hf
  exact castCxSnoc (ssb_conc x (𝐯x') C hxC)
    (castEq (ssb_conc₂ x y (𝐯x') (𝐯y') cs hxcs (NotMem.union hycs hyx))
      (ssb_conc₂ x y (𝐯x') (𝐯y') cs' hxcs' (NotMem.union hycs' hyx))
      (eqC (𝐯x') (𝐯y'))
      (rnSnoc₂ q₂ hx'Γ (NotMem.union (fresh_symm hx'y') hy'Γ)))

/-! ## Computation rules -/

theorem piBetaEF {l l' : Lvl} {Γ : Cx} {A : Ty0} {a : Tm0} {B : Ty 1} {b : Tm 1}
    {x : Atom} (q₀ : (Γ ⨟ x ∶ A ⦂ l) ⊢ b[x] ∶ B[x] ⦂ l') (q₁ : Γ ⊢ a ∶ A ⦂ l)
    (q₂ : x # (B, b)) : Γ ⊢ 𝛌 A b ∙[ A, B ] a ＝ b[a] ∶ B[a] ⦂ l' := by
  have hxB : x # B := notMem_union_left q₂
  have hxb : x # b := notMem_union_right q₂
  exact .piBeta (dom Γ)
    (fun x' hx' => castTm (ssb_conc x (𝐯x') b hxb) (ssb_conc x (𝐯x') B hxB)
      (rnSnoc q₀ hx'))
    q₁ (derivTyOfTm q₁)
    (fun x' hx' => castIsTy (ssb_conc x (𝐯x') B hxB)
      (rnSnoc (derivTyOfTm q₀) hx'))

theorem idBetaEF {l l' : Lvl} {Γ : Cx} {A : Ty0} {C : Ty 2} {a c : Tm0} {x y : Atom}
    (q₀ : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ 𝐈𝐝 A a (𝐯x) ⦂ l) ⊢ C[x][y] ⦂ l')
    (q₁ : Γ ⊢ a ∶ A ⦂ l) (q₂ : Γ ⊢ c ∶ C[a][(𝐫𝐞𝐟𝐥 a : Tm0)] ⦂ l') (q₃ : x # C)
    (q₄ : y # C) :
    Γ ⊢ 𝐉 C a a c (𝐫𝐞𝐟𝐥 a) ＝ c ∶ C[a][(𝐫𝐞𝐟𝐥 a : Tm0)] ⦂ l' := by
  obtain ⟨hyΓx, hI, hOk⟩ := snocOkInv (derivOk q₀)
  obtain ⟨hxΓ, hA, _⟩ := snocOkInv hOk
  have hyx : y # x := notMem_union_right hyΓx
  have hxA : x # A := notMem_union_left (derivFresh hA hxΓ)
  have hxa : x # a := notMem_union_left (derivFresh q₁ hxΓ)
  have eqI : ∀ d : Tm0, (x ≔ d) * (𝐈𝐝 A a (𝐯x) : Ty0) = 𝐈𝐝 A a d := by
    intro d
    rw [sbId, ssbFresh x d A hxA, ssbFresh x d a hxa, sbAtom, Sb.single_eq]
  refine .idBeta (dom Γ) (fun x' y' hf => ?_) q₁ q₂ (derivTyOfTm q₁)
    (fun x' hx' => castIsTy (eqI (𝐯x')) (rnSnoc hI hx'))
  obtain ⟨hy'Γ, hx'Γ, hx'y'⟩ := Fresh₂.inv hf
  exact castCxSnoc (eqI (𝐯x'))
    (castIsTy (ssb_conc₂ x y (𝐯x') (𝐯y') C q₃ (NotMem.union q₄ hyx))
      (rnSnoc₂ q₀ hx'Γ (NotMem.union (fresh_symm hx'y') hy'Γ)))

theorem natBeta₀EF {l : Lvl} {Γ : Cx} {C : Ty 1} {c₀ : Tm0} {cs : Tm 2} {x y : Atom}
    (q₀ : Γ ⊢ c₀ ∶ C[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l)
    (q₁ : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C[x] ⦂ l) ⊢ cs[x][y] ∶ C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] ⦂ l)
    (q₂ : x # (C, cs)) (q₃ : y # cs) :
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ cs 𝐳𝐞𝐫𝐨 ＝ c₀ ∶ C[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l := by
  have hxC : x # C := notMem_union_left q₂
  have hxcs : x # cs := notMem_union_right q₂
  obtain ⟨hyΓx, hCx, _⟩ := snocOkInv (derivOk q₁)
  have hyΓ : y # Γ := notMem_union_left hyΓx
  have hyx : y # x := notMem_union_right hyΓx
  have hyC : y # C := subset_notMem (conc_supp C (𝐳𝐞𝐫𝐨 : Tm0))
    (notMem_union_right (derivFresh q₀ hyΓ))
  have hyxne : y ≠ x := Fset.ne_of_notMem_single hyx
  have eqC : ∀ u v : Tm0,
      ((x ≔ u) ∘/ y ≔ v) * (C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] : Ty0) = C[(𝐬𝐮𝐜𝐜 u : Tm0)] := by
    intro u v
    rw [sb_conc, updateFresh (x ≔ u) y v C hyC, ssbFresh x u C hxC, sbSucc, sbAtom,
      Sb.update_neq _ _ hyxne, Sb.single_eq]
  refine .natBeta₀ (dom Γ) q₀ (fun x' y' hf => ?_)
    (fun x' hx' => castIsTy (ssb_conc x (𝐯x') C hxC) (rnSnoc hCx hx'))
  obtain ⟨hy'Γ, hx'Γ, hx'y'⟩ := Fresh₂.inv hf
  exact castCxSnoc (ssb_conc x (𝐯x') C hxC)
    (castTm (ssb_conc₂ x y (𝐯x') (𝐯y') cs hxcs (NotMem.union q₃ hyx))
      (eqC (𝐯x') (𝐯y'))
      (rnSnoc₂ q₁ hx'Γ (NotMem.union (fresh_symm hx'y') hy'Γ)))

theorem natBetaSEF {l : Lvl} {Γ : Cx} {C : Ty 1} {c₀ a : Tm0} {cs : Tm 2} {x y : Atom}
    (q₀ : Γ ⊢ c₀ ∶ C[(𝐳𝐞𝐫𝐨 : Tm0)] ⦂ l)
    (q₁ : (Γ ⨟ x ∶ 𝐍𝐚𝐭 ⦂ 0 ⨟ y ∶ C[x] ⦂ l) ⊢ cs[x][y] ∶ C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] ⦂ l)
    (q₂ : Γ ⊢ a ∶ 𝐍𝐚𝐭 ⦂ 0) (q₃ : x # (C, cs)) (q₄ : y # cs) :
    Γ ⊢ 𝐧𝐫𝐞𝐜 C c₀ cs (𝐬𝐮𝐜𝐜 a) ＝ cs[a][𝐧𝐫𝐞𝐜 C c₀ cs a] ∶ C[(𝐬𝐮𝐜𝐜 a : Tm0)] ⦂ l := by
  have hxC : x # C := notMem_union_left q₃
  have hxcs : x # cs := notMem_union_right q₃
  obtain ⟨hyΓx, hCx, _⟩ := snocOkInv (derivOk q₁)
  have hyΓ : y # Γ := notMem_union_left hyΓx
  have hyx : y # x := notMem_union_right hyΓx
  have hyC : y # C := subset_notMem (conc_supp C (𝐳𝐞𝐫𝐨 : Tm0))
    (notMem_union_right (derivFresh q₀ hyΓ))
  have hyxne : y ≠ x := Fset.ne_of_notMem_single hyx
  have eqC : ∀ u v : Tm0,
      ((x ≔ u) ∘/ y ≔ v) * (C[(𝐬𝐮𝐜𝐜 (𝐯x) : Tm0)] : Ty0) = C[(𝐬𝐮𝐜𝐜 u : Tm0)] := by
    intro u v
    rw [sb_conc, updateFresh (x ≔ u) y v C hyC, ssbFresh x u C hxC, sbSucc, sbAtom,
      Sb.update_neq _ _ hyxne, Sb.single_eq]
  refine .natBetaS (dom Γ) q₀ (fun x' y' hf => ?_) q₂
    (fun x' hx' => castIsTy (ssb_conc x (𝐯x') C hxC) (rnSnoc hCx hx'))
  obtain ⟨hy'Γ, hx'Γ, hx'y'⟩ := Fresh₂.inv hf
  exact castCxSnoc (ssb_conc x (𝐯x') C hxC)
    (castTm (ssb_conc₂ x y (𝐯x') (𝐯y') cs hxcs (NotMem.union q₄ hyx))
      (eqC (𝐯x') (𝐯y'))
      (rnSnoc₂ q₁ hx'Γ (NotMem.union (fresh_symm hx'y') hy'Γ)))

/-! ## Inversion for `𝚷`, and eta -/

/-- The subject-term half of `piInvGoal`.  Keeping the `Jg` layer separate makes
`piInvGoal Γ (a ∶ A ⦂ l)` reduce to `piInvTm Γ a` for a *variable* `a`, which is what
the `⊢conv` case of the induction needs. -/
private def piInvTm (Γ : Cx) : Tm0 → Prop
  | 𝚷 l l' A B => ∀ x, x # Γ → (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l'
  | _ => True

/-- The statement proved by induction for `piInv`.  Agda's `𝚷⁻¹` only has clauses for
`⊢conv` and `⊢𝚷`, because its argument's subject term is a `𝚷`; Lean's `Deriv.rec`
demands all thirty cases, so the induction runs for this predicate, which is
vacuously true unless the subject term is a `𝚷`. -/
private def piInvGoal (Γ : Cx) : Jg → Prop
  | .ty a _ _ => piInvTm Γ a
  | .eq _ _ _ _ => True

/-- The induction behind `piInv`; see `piInvGoal`. -/
private theorem piInvAux {Γ : Cx} {J : Jg} (q : Γ ⊢ J) : piInvGoal Γ J := by
  induction q using Deriv.rec (motive_1 := fun _ _ => True) with
  | nil => trivial
  | snoc => trivial
  | conv _ _ ih₀ _ => exact ih₀
  | var => trivial
  | univ => trivial
  | @pi Γ l l' A B S q₀ q₁ _ _ =>
      intro x hx
      obtain ⟨x', hx'⟩ := fresh (S, B)
      exact castIsTy (ssb_conc x' (𝐯x) B (notMem_union_right hx'))
        (rnSnoc (q₁ x' (notMem_union_left hx')) hx)
  | lam => trivial
  | app => trivial
  | idF => trivial
  | reflI => trivial
  | j => trivial
  | nat => trivial
  | zero => trivial
  | succ => trivial
  | nrec => trivial
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

theorem piInv {l l' l'' : Lvl} {Γ : Cx} {A C : Ty0} {B : Ty 1} {x : Atom}
    (q : Γ ⊢ 𝚷 l l' A B ∶ C ⦂ l'') (q' : x # Γ) : (Γ ⨟ x ∶ A ⦂ l) ⊢ B[x] ⦂ l' :=
  piInvAux q x q'

theorem piEtaEF {l l' : Lvl} {Γ : Cx} {A : Ty0} {B : Ty 1} {b : Tm0} {x : Atom}
    (q : Γ ⊢ b ∶ 𝚷 l l' A B ⦂ max l l') (q' : x # Γ) :
    Γ ⊢ b ＝ 𝛌 A (x ． (b ∙[ A, B ] 𝐯x)) ∶ 𝚷 l l' A B ⦂ max l l' := by
  obtain ⟨x', hx'⟩ := fresh (Γ, x)
  have hx'Γ : x' # Γ := notMem_union_left hx'
  have hx'x : x' # x := notMem_union_right hx'
  have hfr := derivFresh q q'
  have hxb : x # b := notMem_union_left hfr
  have hxA : x # A := notMem_union_left (notMem_union_right hfr)
  have hxB : x # B :=
    notMem_union_left (notMem_union_right (notMem_union_right hfr))
  have hfr' := derivFresh q hx'Γ
  have hx'B : x' # B :=
    notMem_union_left (notMem_union_right (notMem_union_right hfr'))
  have hBx' : (Γ ⨟ x' ∶ A ⦂ l) ⊢ B[x'] ⦂ l' := piInv (derivTyOfTm q) hx'Γ
  have hA : Γ ⊢ A ⦂ l := (snocOkInv (derivOk hBx')).2.1
  have r : (Γ ⨟ x ∶ A ⦂ l) ⊢ b ∙[ A, B ] 𝐯x ∶ B[x] ⦂ l' :=
    appEF (x := x') (wkDeriv (wkProj hA q') q)
      (.var (Ok.snoc hA q' (derivOk q)) .new)
      (wkDeriv (Weakens.snoc (wkProj hA q') hA (NotMem.union hx'Γ hx'x)
        (wkDeriv (wkProj hA q') hA)) hBx')
      hx'B
  have qlam : Γ ⊢ 𝛌 A (x ． (b ∙[ A, B ] 𝐯x)) ∶ 𝚷 l l' A B ⦂ max l l' :=
    lamEF (x := x)
      (castTm (concAbs' x (b ∙[ A, B ] 𝐯x)).symm rfl r)
      (NotMem.union hxB (fresh_abs x (b ∙[ A, B ] 𝐯x)))
  have eqAbs : ∀ z : Atom,
      (((x ． (b ∙[ A, B ] 𝐯x)) : Tm 1)[(𝐯z : Tm0)] : Tm0) = b ∙[ A, B ] 𝐯z := by
    intro z
    rw [concAbs x (b ∙[ A, B ] 𝐯x) (𝐯z), sbApp, ssbFresh x (𝐯z) b hxb,
      ssbFresh x (𝐯z) A hxA, ssbFresh x (𝐯z) B hxB, sbAtom, Sb.single_eq]
  refine .piEta (dom Γ ∪ ｛ x ｝) q qlam (fun z hz => .symm ?_) hA
  have hzΓ : z # Γ := notMem_union_left hz
  have hzx : z # x := notMem_union_right hz
  refine castEq rfl (eqAbs z) rfl ?_
  refine piBetaEF (x := x) ?_ (.var (Ok.snoc hA hzΓ (derivOk q)) .new)
    (NotMem.union hxB (fresh_abs x (b ∙[ A, B ] 𝐯x)))
  exact castTm (concAbs' x (b ∙[ A, B ] 𝐯x)).symm rfl
    (wkDeriv (Weakens.snoc (wkProj hA hzΓ) hA (NotMem.union q' (fresh_symm hzx))
      (wkDeriv (wkProj hA hzΓ) hA)) r)

/-! ## Context conversion without the helper hypotheses -/

theorem cxEqSnocEF {l : Lvl} {Γ Γ' : Cx} {A A' : Ty0} {x : Atom} (q₀ : ⊢ Γ ＝ Γ')
    (q₁ : Γ ⊢ A ＝ A' ⦂ l) (q₂ : x # (Γ, Γ')) :
    ⊢ (Γ ⨟ x ∶ A ⦂ l) ＝ (Γ' ⨟ x ∶ A' ⦂ l) :=
  .snoc q₀ q₁ q₂ (derivTy₁ q₁) (eqDeriv (derivTy₂ q₁) (cxSymm q₀))

end MLTT

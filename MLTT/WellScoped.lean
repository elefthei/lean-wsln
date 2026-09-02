import MLTT.Ok

/-!
# Provable judgements are well-scoped

Port of `agda-code/agda/MLTT/WellScoped.agda`.

Agda arranges `⊢supp`, `Oksupp` and the scoped support helpers `⊢supp¹`, `⊢supp²`,
`⊢supp＝¹₁`, … as one implicitly mutual cluster: the helpers call `⊢supp` and
`⊢supp` calls the helpers.  Lean needs the cycle broken, so the *pure* `Fset`
content of the helpers is factored out first (`suppConcFresh`, `suppConcFresh₂`,
which take the already-obtained support inclusion as a hypothesis).  `derivSupp`
is then a single application of the joint `Ok`/`Deriv` recursor, `okSupp` is a
plain induction on the context, and the scoped helpers are thin wrappers.
Statements are unchanged.
-/

namespace MLTT

open WSLN
open Fset

/-! ## Support plumbing with no Agda counterpart

Agda writes its support inclusions point-free, composing with the membership
constructors `∈∪₁`/`∈∪₂`.  `subL`/`subR` are the Lean reading of those two
compositions, and `suppConcFresh`/`suppConcFresh₂` are the pure `Fset` kernels of
the scoped support helpers `⊢supp¹`/`⊢supp²`. -/

/-- Left component of an inclusion out of a union; Agda writes `_∘ ∈∪₁`. -/
private theorem subL {s t u : Fset} (h : s ∪ t ⊆ u) : s ⊆ u := fun _ p => h (.unionL p)

/-- Right component of an inclusion out of a union; Agda writes `_∘ ∈∪₂`. -/
private theorem subR {s t u : Fset} (h : s ∪ t ⊆ u) : t ⊆ u := fun _ p => h (.unionR p)

/-- The pure `Fset` kernel of `derivSupp₁`: a term whose concretion at a fresh `x`
is scoped in `D ∪ ｛ x ｝` is itself scoped in `D`. -/
private theorem suppConcFresh {D : Fset} (b : Tm 1) (x : Atom)
    (h : supp (b[x]) ⊆ D ∪ ｛ x ｝) (hx : x # b) : supp b ⊆ D := by
  refine notMem_subset hx (subset_trans ?_ h)
  exact conc_supp b (Trm.atom x)

/-- The pure `Fset` kernel of `derivSupp₂`. -/
private theorem suppConcFresh₂ {D : Fset} (c : Tm 2) (x y : Atom)
    (h : supp (c[x][y]) ⊆ (D ∪ ｛ x ｝) ∪ ｛ y ｝) (hx : x # c) (hy : y # c) :
    supp c ⊆ D := by
  refine notMem_subset hx (notMem_subset hy (subset_trans ?_ h))
  exact conc_supp₂ c (Trm.atom x) (Trm.atom y)

/-! ## Provable judgements are well-scoped -/

theorem derivSupp {Γ : Cx} {J : Jg} (p : Γ ⊢ J) : supp J ⊆ dom Γ := by
  induction p using Deriv.rec
    (motive_1 := fun Γ _ =>
      ∀ (x : Atom) (A : Ty0) (l : Lvl), (x, A, l) isIn Γ → supp A ⊆ dom Γ) with
  | nil _ _ _ hm => cases hm
  | snoc q₀ q₁ hh ih₀ ih₁ x' A' l' hm =>
      cases hm with
      | new => exact subset_trans (subL ih₀) subset_union_left
      | old hm' => exact subset_trans (ih₁ _ _ _ hm') subset_union_left
  | conv q₀ q₁ ih₀ ih₁ => exact union_subset (subL ih₀) (subL (subR ih₁))
  | var q₀ q₁ ih =>
      exact union_subset (single_subset_iff.2 (isIn_dom q₁)) (ih _ _ _ q₁)
  | univ q ih => exact union_subset empty_subset empty_subset
  | @pi _ _ _ _ B S q₀ q₁ ih₀ ih₁ =>
      obtain ⟨x, hx⟩ := fresh (S, B)
      have hxS : x # S := notMem_union_left hx
      have hxB : x # B := notMem_union_right hx
      have hB := suppConcFresh B x (subL (ih₁ x hxS)) hxB
      exact union_subset
        (union_subset (subL ih₀) (union_subset hB empty_subset)) empty_subset
  | @lam _ _ _ _ B b S q₀ h₀ h₁ ih₀ ih₁ ih₂ =>
      obtain ⟨x, hx⟩ := fresh (S, B, b)
      have hxS : x # S := notMem_union_left hx
      have hxB : x # B := notMem_union_left (notMem_union_right hx)
      have hxb : x # b := notMem_union_right (notMem_union_right hx)
      have hA := subL ih₁
      have hb := suppConcFresh b x (subL (ih₀ x hxS)) hxb
      have hB := suppConcFresh B x (subL (ih₂ x hxS)) hxB
      exact union_subset
        (union_subset hA (union_subset hb empty_subset))
        (union_subset hA (union_subset hB empty_subset))
  | @app _ _ _ _ B a _ S q₀ q₁ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      obtain ⟨x, hx⟩ := fresh (S, B)
      have hxS : x # S := notMem_union_left hx
      have hxB : x # B := notMem_union_right hx
      have hB := suppConcFresh B x (subL (ih₂ x hxS)) hxB
      have ha := subL ih₁
      exact union_subset
        (union_subset (subL ih₀)
          (union_subset (subL ih₃) (union_subset hB (union_subset ha empty_subset))))
        (subset_trans (supp_conc B a) (union_subset hB ha))
  | idF q₀ q₁ h ih₀ ih₁ ih₂ =>
      exact union_subset
        (union_subset (subL ih₂)
          (union_subset (subL ih₀) (union_subset (subL ih₁) empty_subset)))
        empty_subset
  | reflI q h ih₀ ih₁ =>
      exact union_subset (union_subset (subL ih₀) empty_subset)
        (union_subset (subL ih₁)
          (union_subset (subL ih₀) (union_subset (subL ih₀) empty_subset)))
  | @j _ _ _ _ C _ b _ e S q₀ q₁ q₂ q₃ q₄ h₀ h₁ ih₀ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
      obtain ⟨y, hy⟩ := fresh (C, S)
      have hyC : y # C := notMem_union_left hy
      have hyS : y # S := notMem_union_right hy
      obtain ⟨x, hx⟩ := fresh (C, y, S)
      have hxC : x # C := notMem_union_left hx
      have hxyS : x ∉ᶠ ｛ y ｝ ∪ S := notMem_union_right hx
      have hfr : x # y # S :=
        Distinct.cons hyS (Distinct.cons hxyS Distinct.nil)
      have hC := suppConcFresh₂ C x y (subL (ih₀ x y hfr)) hxC hyC
      have hb := subL ih₂
      have he := subL ih₄
      exact union_subset
        (union_subset hC
          (union_subset (subL ih₁)
            (union_subset hb
              (union_subset (subL ih₃) (union_subset he empty_subset)))))
        (subset_trans (supp_conc₂ C b e)
          (union_subset (union_subset hC hb) he))
  | nat q => exact union_subset empty_subset empty_subset
  | zero q => exact union_subset empty_subset empty_subset
  | succ q ih => exact union_subset ih empty_subset
  | @nrec _ _ C _ a cs S q₀ q₁ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      obtain ⟨y, hy⟩ := fresh (cs, S)
      have hycs : y # cs := notMem_union_left hy
      have hyS : y # S := notMem_union_right hy
      obtain ⟨x, hx⟩ := fresh (C, cs, y, S)
      have hxC : x # C := notMem_union_left hx
      have hxcs : x # cs := notMem_union_left (notMem_union_right hx)
      have hxy : x # y :=
        notMem_union_left (notMem_union_right (notMem_union_right hx))
      have hxS : x # S :=
        notMem_union_right (notMem_union_right (notMem_union_right hx))
      have hfr : x # y # S := Fresh₂.intro hyS hxS hxy
      have hC := suppConcFresh C x (subL (ih₃ x hxS)) hxC
      have hcs := suppConcFresh₂ cs x y (subL (ih₁ x y hfr)) hxcs hycs
      have ha := subL ih₂
      exact union_subset
        (union_subset hC
          (union_subset (subL ih₀)
            (union_subset hcs (union_subset ha empty_subset))))
        (subset_trans (supp_conc C a) (union_subset hC ha))
  | refl q ih => exact union_subset (subL ih) (union_subset (subL ih) (subR ih))
  | symm q ih =>
      exact union_subset (subL (subR ih))
        (union_subset (subL ih) (subR (subR ih)))
  | trans q₀ q₁ ih₀ ih₁ =>
      exact union_subset (subL ih₀)
        (union_subset (subL (subR ih₁)) (subR (subR ih₀)))
  | eqConv q₀ q₁ ih₀ ih₁ =>
      exact union_subset (subL ih₀)
        (union_subset (subL (subR ih₀)) (subL (subR ih₁)))
  | @piCong _ _ _ _ _ B B' S q₀ q₁ h ih₀ ih₁ ih₂ =>
      obtain ⟨x, hx⟩ := fresh (S, B, B')
      have hxS : x # S := notMem_union_left hx
      have hxB : x # B := notMem_union_left (notMem_union_right hx)
      have hxB' : x # B' := notMem_union_right (notMem_union_right hx)
      have hB := suppConcFresh B x (subL (ih₁ x hxS)) hxB
      have hB' := suppConcFresh B' x (subL (subR (ih₁ x hxS))) hxB'
      exact union_subset
        (union_subset (subL ih₂) (union_subset hB empty_subset))
        (union_subset
          (union_subset (subL (subR ih₀)) (union_subset hB' empty_subset))
          empty_subset)
  | @lamCong _ _ _ _ _ B b b' S q₀ q₁ h₀ h₁ ih₀ ih₁ ih₂ ih₃ =>
      obtain ⟨x, hx⟩ := fresh (S, B, b, b')
      have hxS : x # S := notMem_union_left hx
      have hxB : x # B := notMem_union_left (notMem_union_right hx)
      have hxb : x # b :=
        notMem_union_left (notMem_union_right (notMem_union_right hx))
      have hxb' : x # b' :=
        notMem_union_right (notMem_union_right (notMem_union_right hx))
      have hA := subL ih₂
      have hb := suppConcFresh b x (subL (ih₁ x hxS)) hxb
      have hb' := suppConcFresh b' x (subL (subR (ih₁ x hxS))) hxb'
      have hB := suppConcFresh B x (subL (ih₃ x hxS)) hxB
      exact union_subset
        (union_subset hA (union_subset hb empty_subset))
        (union_subset
          (union_subset (subL (subR ih₀)) (union_subset hb' empty_subset))
          (union_subset hA (union_subset hB empty_subset)))
  | @appCong _ _ _ _ _ B B' a _ _ _ S q₀ q₁ q₂ q₃ h₀ h₁ ih₀ ih₁ ih₂ ih₃ ih₄ ih₅ =>
      obtain ⟨x, hx⟩ := fresh (S, B, B')
      have hxS : x # S := notMem_union_left hx
      have hxB : x # B := notMem_union_left (notMem_union_right hx)
      have hxB' : x # B' := notMem_union_right (notMem_union_right hx)
      have hB := suppConcFresh B x (subL (ih₅ x hxS)) hxB
      have hB' := suppConcFresh B' x (subL (subR (ih₁ x hxS))) hxB'
      have ha := subL ih₃
      exact union_subset
        (union_subset (subL ih₂)
          (union_subset (subL ih₄) (union_subset hB (union_subset ha empty_subset))))
        (union_subset
          (union_subset (subL (subR ih₂))
            (union_subset (subL (subR ih₀))
              (union_subset hB'
                (union_subset (subL (subR ih₃)) empty_subset))))
          (subset_trans (supp_conc B a) (union_subset hB ha)))
  | idCong q₀ q₁ q₂ ih₀ ih₁ ih₂ =>
      exact union_subset
        (union_subset (subL ih₀)
          (union_subset (subL ih₁) (union_subset (subL ih₂) empty_subset)))
        (union_subset
          (union_subset (subL (subR ih₀))
            (union_subset (subL (subR ih₁))
              (union_subset (subL (subR ih₂)) empty_subset)))
          empty_subset)
  | reflCong q h ih₀ ih₁ =>
      exact union_subset (union_subset (subL ih₀) empty_subset)
        (union_subset (union_subset (subL (subR ih₀)) empty_subset)
          (union_subset (subL ih₁)
            (union_subset (subL ih₀) (union_subset (subL ih₀) empty_subset))))
  | @jCong _ _ _ _ C C' _ _ b _ _ _ e _ S q₀ q₁ q₂ q₃ q₄ h₀ h₁
      ih₀ ih₁ ih₂ ih₃ ih₄ ih₅ ih₆ =>
      obtain ⟨y, hy⟩ := fresh (C, C', S)
      have hyC : y # C := notMem_union_left hy
      have hyC' : y # C' := notMem_union_left (notMem_union_right hy)
      have hyS : y # S := notMem_union_right (notMem_union_right hy)
      obtain ⟨x, hx⟩ := fresh (C, C', y, S)
      have hxC : x # C := notMem_union_left hx
      have hxC' : x # C' := notMem_union_left (notMem_union_right hx)
      have hxyS : x ∉ᶠ ｛ y ｝ ∪ S := notMem_union_right (notMem_union_right hx)
      have hfr : x # y # S :=
        Distinct.cons hyS (Distinct.cons hxyS Distinct.nil)
      have hC := suppConcFresh₂ C x y (subL (ih₀ x y hfr)) hxC hyC
      have hC' := suppConcFresh₂ C' x y (subL (subR (ih₀ x y hfr))) hxC' hyC'
      have hb := subL ih₂
      have he := subL ih₄
      exact union_subset
        (union_subset hC
          (union_subset (subL ih₁)
            (union_subset hb
              (union_subset (subL ih₃) (union_subset he empty_subset)))))
        (union_subset
          (union_subset hC'
            (union_subset (subL (subR ih₁))
              (union_subset (subL (subR ih₂))
                (union_subset (subL (subR ih₃))
                  (union_subset (subL (subR ih₄)) empty_subset)))))
          (subset_trans (supp_conc₂ C b e)
            (union_subset (union_subset hC hb) he)))
  | succCong q ih =>
      exact union_subset (union_subset (subL ih) empty_subset)
        (union_subset (union_subset (subL (subR ih)) empty_subset) empty_subset)
  | @nrecCong _ _ C C' _ _ a _ cs cs' S q₀ q₁ q₂ q₃ h ih₀ ih₁ ih₂ ih₃ ih₄ =>
      obtain ⟨y, hy⟩ := fresh (C, C', cs, cs', S)
      have hycs : y # cs :=
        notMem_union_left (notMem_union_right (notMem_union_right hy))
      have hycs' : y # cs' :=
        notMem_union_left
          (notMem_union_right (notMem_union_right (notMem_union_right hy)))
      have hyS : y # S :=
        notMem_union_right
          (notMem_union_right (notMem_union_right (notMem_union_right hy)))
      obtain ⟨x, hx⟩ := fresh (C, C', cs, cs', y, S)
      have hxC : x # C := notMem_union_left hx
      have hxC' : x # C' := notMem_union_left (notMem_union_right hx)
      have hxcs : x # cs :=
        notMem_union_left (notMem_union_right (notMem_union_right hx))
      have hxcs' : x # cs' :=
        notMem_union_left
          (notMem_union_right (notMem_union_right (notMem_union_right hx)))
      have hxy : x # y :=
        notMem_union_left
          (notMem_union_right
            (notMem_union_right (notMem_union_right (notMem_union_right hx))))
      have hxS : x # S :=
        notMem_union_right
          (notMem_union_right
            (notMem_union_right (notMem_union_right (notMem_union_right hx))))
      have hfr : x # y # S := Fresh₂.intro hyS hxS hxy
      have hC := suppConcFresh C x (subL (ih₀ x hxS)) hxC
      have hC' := suppConcFresh C' x (subL (subR (ih₀ x hxS))) hxC'
      have hcs := suppConcFresh₂ cs x y (subL (ih₂ x y hfr)) hxcs hycs
      have hcs' := suppConcFresh₂ cs' x y (subL (subR (ih₂ x y hfr))) hxcs' hycs'
      have ha := subL ih₃
      exact union_subset
        (union_subset hC
          (union_subset (subL ih₁)
            (union_subset hcs (union_subset ha empty_subset))))
        (union_subset
          (union_subset hC'
            (union_subset (subL (subR ih₁))
              (union_subset hcs'
                (union_subset (subL (subR ih₃)) empty_subset))))
          (subset_trans (supp_conc C a) (union_subset hC ha)))
  | @piBeta _ _ _ _ a B b S q₀ q₁ h₀ h₁ ih₀ ih₁ ih₂ ih₃ =>
      obtain ⟨x, hx⟩ := fresh (B, b, S)
      have hxB : x # B := notMem_union_left hx
      have hxb : x # b := notMem_union_left (notMem_union_right hx)
      have hxS : x # S := notMem_union_right (notMem_union_right hx)
      have hA := subL ih₂
      have hb := suppConcFresh b x (subL (ih₀ x hxS)) hxb
      have hB := suppConcFresh B x (subL (ih₃ x hxS)) hxB
      have ha := subL ih₁
      exact union_subset
        (union_subset
          (union_subset hA (union_subset hb empty_subset))
          (union_subset hA (union_subset hB (union_subset ha empty_subset))))
        (union_subset
          (subset_trans (supp_conc b a) (union_subset hb ha))
          (subset_trans (supp_conc B a) (union_subset hB ha)))
  | @idBeta _ _ _ _ C a _ S q₀ q₁ q₂ h₀ h₁ ih₀ ih₁ ih₂ ih₃ ih₄ =>
      obtain ⟨y, hy⟩ := fresh (C, S)
      have hyC : y # C := notMem_union_left hy
      have hyS : y # S := notMem_union_right hy
      obtain ⟨x, hx⟩ := fresh (C, y, S)
      have hxC : x # C := notMem_union_left hx
      have hxyS : x ∉ᶠ ｛ y ｝ ∪ S := notMem_union_right hx
      have hfr : x # y # S :=
        Distinct.cons hyS (Distinct.cons hxyS Distinct.nil)
      have hC := suppConcFresh₂ C x y (subL (ih₀ x y hfr)) hxC hyC
      have ha := subL ih₁
      have hc := subL ih₂
      exact union_subset
        (union_subset hC
          (union_subset ha
            (union_subset ha
              (union_subset hc
                (union_subset (union_subset ha empty_subset) empty_subset)))))
        (union_subset hc
          (subset_trans (supp_conc₂ C a (𝐫𝐞𝐟𝐥 a))
            (union_subset (union_subset hC ha)
              (union_subset ha empty_subset))))
  | @natBeta₀ _ _ C _ cs S q₀ q₁ h ih₀ ih₁ ih₂ =>
      obtain ⟨y, hy⟩ := fresh (cs, S)
      have hycs : y # cs := notMem_union_left hy
      have hyS : y # S := notMem_union_right hy
      obtain ⟨x, hx⟩ := fresh (C, cs, y, S)
      have hxC : x # C := notMem_union_left hx
      have hxcs : x # cs := notMem_union_left (notMem_union_right hx)
      have hxy : x # y :=
        notMem_union_left (notMem_union_right (notMem_union_right hx))
      have hxS : x # S :=
        notMem_union_right (notMem_union_right (notMem_union_right hx))
      have hfr : x # y # S := Fresh₂.intro hyS hxS hxy
      have hC := suppConcFresh C x (subL (ih₂ x hxS)) hxC
      have hcs := suppConcFresh₂ cs x y (subL (ih₁ x y hfr)) hxcs hycs
      exact union_subset
        (union_subset hC
          (union_subset (subL ih₀)
            (union_subset hcs (union_subset empty_subset empty_subset))))
        (union_subset (subL ih₀) (subR ih₀))
  | @natBetaS _ _ C c₀ a cs S q₀ q₁ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      obtain ⟨y, hy⟩ := fresh (cs, S)
      have hycs : y # cs := notMem_union_left hy
      have hyS : y # S := notMem_union_right hy
      obtain ⟨x, hx⟩ := fresh (C, cs, y, S)
      have hxC : x # C := notMem_union_left hx
      have hxcs : x # cs := notMem_union_left (notMem_union_right hx)
      have hxy : x # y :=
        notMem_union_left (notMem_union_right (notMem_union_right hx))
      have hxS : x # S :=
        notMem_union_right (notMem_union_right (notMem_union_right hx))
      have hfr : x # y # S := Fresh₂.intro hyS hxS hxy
      have hC := suppConcFresh C x (subL (ih₃ x hxS)) hxC
      have hcs := suppConcFresh₂ cs x y (subL (ih₁ x y hfr)) hxcs hycs
      have hc₀ := subL ih₀
      have ha := subL ih₂
      exact union_subset
        (union_subset hC
          (union_subset hc₀
            (union_subset hcs
              (union_subset (union_subset ha empty_subset) empty_subset))))
        (union_subset
          (subset_trans (supp_conc₂ cs a (𝐧𝐫𝐞𝐜 C c₀ cs a))
            (union_subset (union_subset hcs ha)
              (union_subset hC
                (union_subset hc₀
                  (union_subset hcs (union_subset ha empty_subset))))))
          (subset_trans (supp_conc C (𝐬𝐮𝐜𝐜 a))
            (union_subset hC (union_subset ha empty_subset))))
  | @piEta _ _ _ _ B _ _ S q₀ q₁ q₂ h ih₀ ih₁ ih₂ ih₃ =>
      obtain ⟨x, hx⟩ := fresh (B, S)
      have hxB : x # B := notMem_union_left hx
      have hxS : x # S := notMem_union_right hx
      have hB := suppConcFresh B x (subR (subR (ih₂ x hxS))) hxB
      exact union_subset (subL ih₀)
        (union_subset (subL ih₁)
          (union_subset (subL ih₃) (union_subset hB empty_subset)))

theorem okSupp {Γ : Cx} {x : Atom} {A : Ty0} {l : Lvl} (p : Ok Γ)
    (q : (x, A, l) isIn Γ) : supp A ⊆ dom Γ := by
  revert p q
  induction Γ with
  | nil => intro _ q; cases q
  | snoc Γ' y B l' ih =>
      intro p q
      cases q with
      | new =>
          cases p with
          | snoc q₀ _ _ => exact subset_trans (subL (derivSupp q₀)) subset_union_left
      | old q' =>
          cases p with
          | snoc _ _ hh => exact subset_trans (ih hh q') subset_union_left

theorem derivSupp₁ {Γ : Cx} {A B : Ty0} {l l' : Lvl} (b : Tm 1) (x : Atom)
    (p : (Γ ⨟ x ∶ A ⦂ l) ⊢ b[x] ∶ B ⦂ l') (q : x # b) : supp b ⊆ dom Γ :=
  suppConcFresh b x (subL (derivSupp p)) q

theorem derivSupp₂ {Γ : Cx} {A B C : Ty0} {l l' l'' : Lvl} (c : Tm 2) (x y : Atom)
    (p : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢ c[x][y] ∶ C ⦂ l'') (q : x # c) (q' : y # c) :
    supp c ⊆ dom Γ :=
  suppConcFresh₂ c x y (subL (derivSupp p)) q q'

theorem derivSuppEq₁₁ {Γ : Cx} {A B : Ty0} {b' : Tm0} {l l' : Lvl} (b : Tm 1)
    (x : Atom) (p : (Γ ⨟ x ∶ A ⦂ l) ⊢ b[x] ＝ b' ∶ B ⦂ l') (q : x # b) :
    supp b ⊆ dom Γ :=
  suppConcFresh b x (subL (derivSupp p)) q

theorem derivSuppEq₁₂ {Γ : Cx} {A B : Ty0} {b' : Tm0} {l l' : Lvl} (b : Tm 1)
    (x : Atom) (p : (Γ ⨟ x ∶ A ⦂ l) ⊢ b' ＝ b[x] ∶ B ⦂ l') (q : x # b) :
    supp b ⊆ dom Γ :=
  suppConcFresh b x (subL (subR (derivSupp p))) q

theorem derivSuppEq₁₃ {Γ : Cx} {A : Ty0} {b b' : Tm0} {l l' : Lvl} (B : Tm 1)
    (x : Atom) (p : (Γ ⨟ x ∶ A ⦂ l) ⊢ b ＝ b' ∶ B[x] ⦂ l') (q : x # B) :
    supp B ⊆ dom Γ :=
  suppConcFresh B x (subR (subR (derivSupp p))) q

theorem derivSuppEq₂₁ {Γ : Cx} {A B C : Ty0} {c' : Tm0} {l l' l'' : Lvl} (c : Tm 2)
    (x y : Atom) (p : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢ c[x][y] ＝ c' ∶ C ⦂ l'')
    (q : x # c) (q' : y # c) : supp c ⊆ dom Γ :=
  suppConcFresh₂ c x y (subL (derivSupp p)) q q'

theorem derivSuppEq₂₂ {Γ : Cx} {A B C : Ty0} {c' : Tm0} {l l' l'' : Lvl} (c : Tm 2)
    (x y : Atom) (p : (Γ ⨟ x ∶ A ⦂ l ⨟ y ∶ B ⦂ l') ⊢ c' ＝ c[x][y] ∶ C ⦂ l'')
    (q : x # c) (q' : y # c) : supp c ⊆ dom Γ :=
  suppConcFresh₂ c x y (subL (subR (derivSupp p))) q q'

/-! ## Freshness property of provable judgements -/

theorem derivFresh {Γ : Cx} {J : Jg} {x : Atom} (p : Γ ⊢ J) (q : x # Γ) : x # J :=
  subset_notMem (derivSupp p) q

/-! ## Convertible contexts have extensionally equal domains -/

theorem domEq {Γ Γ' : Cx} (p : ⊢ Γ ＝ Γ') : dom Γ ⊆ dom Γ' := by
  induction p with
  | nil => exact subset_refl
  | snoc q₀ q₁ q₂ h₀ h₁ ih => exact union_subset_union ih subset_refl

end MLTT

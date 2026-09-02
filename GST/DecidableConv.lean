import GST.Normalization

/-!
# Decidability of typing and of βη-conversion

Port of `agda-code/agda/GST/DecidableConv.agda`.

Concretion `b[x]` is not a substructure of `b` but has the same size, so type
synthesis recurses on a size bound, exactly as in Agda: `synthLe s Γ a h` synthesises
a type for `a` given `a.size ≤ s`, by structural recursion on the fuel `s`.

Agda's mutually recursive `cond≤TmTy?` is a wrapper around `cond≤Tm∃Ty?`; here it is
factored as `decOfSynth`, which post-processes a synthesis result, so the recursion
stays single and structural.

The decisions are `WSLN.Dec`-valued rather than `Decidable`-valued: the typing and
conversion judgements live in `Type`, not in `Prop`.  They are plain definitions, not
instances: `decide` should never be pointed at them by accident.
-/

namespace GST

open WSLN

/-! ## Decidability of the typing relation -/

/-- Lean-only: size bookkeeping for `synthLe` — the first operand of a sized
operator fits under the fuel.  Replaces Agda's `where`-local `≤s₀`-style bounds.
Stated over bare `Nat.max` so it applies definitionally to `Trm.size` of the
pattern constructors.  Proofs deliberately avoid `omega`/`simp`, which would pull
`Classical.choice` into `tyDec`/`convDec` (the `#guard_msgs` gates below enforce
this). -/
theorem max_le_succ₁ {x y s : Nat} (h : max x y + 1 ≤ s + 1) : x ≤ s :=
  Nat.le_trans (Nat.le_max_left x y) (Nat.le_of_succ_le_succ h)

/-- Lean-only: the second operand of a sized operator fits under the fuel. -/
theorem max_le_succ₂ {x y z s : Nat} (h : max x (max y z) + 1 ≤ s + 1) : y ≤ s :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_left y z) (Nat.le_max_right x (max y z)))
    (Nat.le_of_succ_le_succ h)

/-- Lean-only: the third operand of a sized operator fits under the fuel. -/
theorem max_le_succ₃ {x y z w s : Nat}
    (h : max x (max y (max z w)) + 1 ≤ s + 1) : z ≤ s :=
  Nat.le_trans
    (Nat.le_trans (Nat.le_max_left z w)
      (Nat.le_trans (Nat.le_max_right y (max z w))
        (Nat.le_max_right x (max y (max z w)))))
    (Nat.le_of_succ_le_succ h)

/-- Agda: the `with A ≐ A'` step of `cond≤TmTy?` (GST/DecidableConv.agda). -/
def decOfSynth {S : Fset} {Γ : Cx S} {a : Tm0} (A : Ty) :
    Dec (Σ A' : Ty, Γ ⊢ a ∶ A') → Dec (Γ ⊢ a ∶ A)
  | .no hn => .no fun p => hn ⟨A, p⟩
  | .yes ⟨A', p⟩ =>
      if e : A = A' then .yes (castTy e.symm p) else .no fun p' => e (svTy p' p)

/-- Agda: `cond≤Tm∃Ty?` (GST/DecidableConv.agda). -/
def synthLe : (s : Nat) → {S : Fset} → (Γ : Cx S) → (a : Tm0) → a.size ≤ s →
    Dec (Σ A : Ty, Γ ⊢ a ∶ A)
  | _, _, _, .var i, _ => i.elim0
  | _, _, Γ, 𝐯x, _ =>
      match memDec x Γ with
      | isFalse hn => .no fun p =>
          match p with
          | ⟨_, .var q⟩ => hn (isIn_dom q)
      | isTrue hm =>
          let ⟨A, q⟩ := dom_isIn Γ hm
          .yes ⟨A, .var q⟩
  | 0, _, _, 𝛌 _ _, h => absurd h (Nat.not_succ_le_zero _)
  | s + 1, _, Γ, 𝛌 A b, h =>
      let f := freshFor b (dom Γ)
      have hΓ : f.val ∉ᶠ dom Γ := f.property.2
      have hb : f.val # b := f.property.1
      match synthLe s (Γ ⨟ f.val ∶ A ∣ hΓ) (b[f.val])
        (size_conc_le b f.val (max_le_succ₁ h)) with
      | .no hn => .no fun p =>
          match p with
          | ⟨_, pp⟩ => hn ⟨_, (lamInv hΓ pp hb).2.2⟩
      | .yes ⟨B, p⟩ => .yes ⟨A ⇒ B, .lam p hb⟩
  | 0, _, _, _ ∙ _, h => absurd h (Nat.not_succ_le_zero _)
  | s + 1, _, Γ, b ∙ a, h =>
      match synthLe s Γ b (max_le_succ₁ h) with
      | .no hn => .no fun p =>
          match p with
          | ⟨_, .app p₀ _⟩ => hn ⟨_, p₀⟩
      | .yes ⟨C, p⟩ =>
        match synthLe s Γ a (max_le_succ₂ h) with
        | .no hn => .no fun p =>
            match p with
            | ⟨_, .app _ p₁⟩ => hn ⟨_, p₁⟩
        | .yes ⟨A, p'⟩ =>
          match arrowDec C A with
          | .no hn => .no fun z =>
              match z with
              | ⟨B, .app q q'⟩ => by
                  cases svTy p' q'
                  cases svTy p q
                  exact hn ⟨B, rfl⟩
          | .yes ⟨B, e⟩ => .yes ⟨B, .app (castTy e p) p'⟩
  | _, _, _, 𝐳𝐞𝐫𝐨, _ => .yes ⟨𝐍𝐚𝐭, .zero⟩
  | 0, _, _, 𝐬𝐮𝐜𝐜 _, h => absurd h (Nat.not_succ_le_zero _)
  | s + 1, _, Γ, 𝐬𝐮𝐜𝐜 a, h =>
      match decOfSynth 𝐍𝐚𝐭 (synthLe s Γ a (max_le_succ₁ h)) with
      | .no hn => .no fun z =>
          match z with
          | ⟨_, .succ p⟩ => hn p
      | .yes p => .yes ⟨𝐍𝐚𝐭, .succ p⟩
  | 0, _, _, 𝐧𝐫𝐞𝐜 _ _ _, h => absurd h (Nat.not_succ_le_zero _)
  | s + 1, _, Γ, 𝐧𝐫𝐞𝐜 c₀ cs a, h =>
      match synthLe s Γ c₀ (max_le_succ₁ h) with
      | .no hn => .no fun z =>
          match z with
          | ⟨_, .nrec p _ _⟩ => hn ⟨_, p⟩
      | .yes ⟨C, p₀⟩ =>
        match decOfSynth (𝐍𝐚𝐭 ⇒ C ⇒ C) (synthLe s Γ cs (max_le_succ₂ h)) with
        | .no hn => .no fun z =>
            match z with
            | ⟨_, .nrec q q' _⟩ => by cases svTy q p₀; exact hn q'
        | .yes p₁ =>
          match decOfSynth 𝐍𝐚𝐭 (synthLe s Γ a (max_le_succ₃ h)) with
          | .no hn => .no fun z =>
              match z with
              | ⟨_, .nrec _ _ p⟩ => hn p
          | .yes p₂ => .yes ⟨C, .nrec p₀ p₁ p₂⟩

/-- Agda: `cond≤TmTy?` (GST/DecidableConv.agda). -/
def tyDecLe (s : Nat) {S : Fset} (Γ : Cx S) (a : Tm0) (h : a.size ≤ s) (A : Ty) :
    Dec (Γ ⊢ a ∶ A) := decOfSynth A (synthLe s Γ a h)

/-- Agda: `⊢∶?` (GST/DecidableConv.agda). -/
def tyDec {S : Fset} (Γ : Cx S) (A : Ty) (a : Tm0) : Dec (Γ ⊢ a ∶ A) :=
  tyDecLe a.size Γ a (Nat.le_refl _) A

/-! ## Decidability of the conversion relation -/

/-- Agda: `condEq?` (GST/DecidableConv.agda). -/
def convDecOfTy {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} (q : Γ ⊢ a ∶ A)
    (q' : Γ ⊢ a' ∶ A) : Dec (Γ ⊢ a ＝ a' ∶ A) :=
  Dec.ofIff (NF1' Γ q q') (NF2 Γ q q') (Dec.ofDecidable inferInstance)

/-- Agda: `⊢＝?` (GST/DecidableConv.agda). -/
def convDec {S : Fset} (Γ : Cx S) (A : Ty) (a a' : Tm0) : Dec (Γ ⊢ a ＝ a' ∶ A) :=
  condDec (fun q => ⟨convTy₁ q, convTy₂ q⟩)
    (Dec.and (tyDec Γ A a) (tyDec Γ A a')) (fun p => convDecOfTy p.1 p.2)

/-! ## Checks

The axiom reports of the six headline results, pinned with `#guard_msgs`: a mismatch
— an added axiom, or a `sorryAx` from an unfinished proof — is a compile error. -/

section Checks

/-- info: 'GST.svTy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms svTy

/-- info: 'GST.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sound

/-- info: 'GST.NF1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NF1

/-- info: 'GST.NF2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NF2

/-- info: 'GST.tyDec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tyDec

/-- info: 'GST.convDec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms convDec

end Checks

end GST

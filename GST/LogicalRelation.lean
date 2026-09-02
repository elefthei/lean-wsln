import GST.TermSemantics

/-!
# The glueing logical relation

Port of `agda-code/agda/GST/LogicalRelation.agda`.

`Glue Γ a A 𝓪` is Agda's `⟦ Γ ⊢ a ∶ A ⟧≈ 𝓪`, defined by recursion on the type `A`, and
`GlueSb Γ' σ Γ 𝓼` is Agda's `⟦ Γ' ⊢ˢ σ ∶ Γ ⟧≈ 𝓼`, defined by recursion on the context.
Both are `Type`-valued: at `𝐍𝐚𝐭` the relation *is* a conversion derivation.

The file ends with the fundamental property `FP` and its instance `FPSb₀` at the
initial environment.
-/

namespace GST

open WSLN

/-! ## The glueing relation -/

/-- Agda: `⟦_⊢_∶_⟧≈_` (GST/LogicalRelation.agda). -/
def Glue : {S : Fset} → (Γ : Cx S) → Tm0 → (A : Ty) → Psh.El (𝓓 A) Γ → Type
  | _, Γ, a, 𝐍𝐚𝐭, 𝓪 => Γ ⊢ a ＝ 𝓪.nt ∶ 𝐍𝐚𝐭
  | _, Γ, b, A ⇒ B, 𝓯 =>
      (Γ ⊢ b ∶ A ⇒ B) ×
        ({S' : Fset} → {Γ' : Cx S'} → {a : Tm0} → (p : RnHom Γ' Γ) →
          (𝓪 : Psh.El (𝓓 A) Γ') → Glue Γ' a A 𝓪 →
          Glue Γ' ((p.rn * b) ∙ a) B (𝓯.hom.map (p, 𝓪)))

/-- Transport the glueing relation along an equality of terms (Agda uses `subst`). -/
def castGlue {S : Fset} {Γ : Cx S} {A : Ty} {a a' : Tm0} {𝓪 : Psh.El (𝓓 A) Γ}
    (e : a = a') (r : Glue Γ a A 𝓪) : Glue Γ a' A 𝓪 := e ▸ r

/-- Agda: `⟦_⊢ˢ_∶_⟧≈_` (GST/LogicalRelation.agda). -/
def GlueSb : {S S' : Fset} → (Γ' : Cx S') → Sb sig → (Γ : Cx S) →
    Psh.El (𝓔 Γ) Γ' → Type
  | _, _, _, _, .nil, _ => PUnit
  | _, _, Γ', σ, .snoc Γ x A _, 𝓼 => GlueSb Γ' σ Γ 𝓼.1 × Glue Γ' (σ x) A 𝓼.2

/-! ## Escape -/

/-- Agda: `⟦esc⟧` (GST/LogicalRelation.agda). -/
def glueEsc : {A : Ty} → {S : Fset} → {Γ : Cx S} → {a : Tm0} →
    {𝓪 : Psh.El (𝓓 A) Γ} → Glue Γ a A 𝓪 → Γ ⊢ a ∶ A
  | 𝐍𝐚𝐭, _, _, _, _, r => convTy₁ r
  | _ ⇒ _, _, _, _, _, r => r.1

/-- Agda: `⟦escˢ⟧` (GST/LogicalRelation.agda). -/
def glueEscSb : {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {σ : Sb sig} →
    {𝓼 : Psh.El (𝓔 Γ) Γ'} → GlueSb Γ' σ Γ 𝓼 → Γ' ⊢ˢ σ ∶ Γ
  | _, _, .nil, _, _, _, _ => .nil
  | _, _, .snoc _ _ _ _, _, _, _, r => .snoc (glueEscSb r.1) (glueEsc r.2)

/-! ## Congruence -/

/-- Agda: `⟦cong⟧` (GST/LogicalRelation.agda). -/
def glueCong : (A : Ty) → {S : Fset} → {Γ : Cx S} → {a a' : Tm0} →
    (𝓪 𝓪' : Psh.El (𝓓 A) Γ) → Glue Γ a A 𝓪 → (Γ ⊢ a' ＝ a ∶ A) →
    ((𝓓 A).obj Γ ∋ 𝓪 ~ 𝓪') → Glue Γ a' A 𝓪'
  | 𝐍𝐚𝐭, _, _, _, _, _, _, q₀, q₁, q₂ => castEq rfl q₂ (.trans q₁ q₀)
  | _ ⇒ B, _, _, _, _, 𝓯, 𝓯', q₀, q₁, q₂ =>
      ⟨convTy₁ q₁, fun p 𝓪 r =>
        glueCong B (𝓯.hom.map (p, 𝓪)) (𝓯'.hom.map (p, 𝓪)) (q₀.2 p 𝓪 r)
          (.app (rnConv p.pf q₁) (.refl (glueEsc r))) (q₂ (p, 𝓪))⟩

/-- Agda: `⟦congˢ⟧` (GST/LogicalRelation.agda). -/
def glueCongSb : {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {σ σ' : Sb sig} →
    (𝓼 𝓼' : Psh.El (𝓔 Γ) Γ') → GlueSb Γ' σ Γ 𝓼 → (Γ' ⊢ˢ σ' ＝ σ ∶ Γ) →
    ((𝓔 Γ).obj Γ' ∋ 𝓼 ~ 𝓼') → GlueSb Γ' σ' Γ 𝓼'
  | _, _, .nil, _, _, _, _, _, _, _, _ => ⟨⟩
  | _, _, .snoc _ _ A _, _, _, _, 𝓼, 𝓼', r, .snoc q₂ q₃, e =>
      ⟨glueCongSb 𝓼.1 𝓼'.1 r.1 q₂ e.1, glueCong A 𝓼.2 𝓼'.2 r.2 q₃ e.2⟩

/-! ## Reification and reflection -/

mutual

/-- Agda: `⟦↓⟧` (GST/LogicalRelation.agda). -/
def glueReify : {A : Ty} → {S : Fset} → {Γ : Cx S} → {a : Tm0} →
    {𝓪 : Psh.El (𝓓 A) Γ} → Glue Γ a A 𝓪 → Γ ⊢ a ＝ reifyTm A 𝓪 ∶ A
  | 𝐍𝐚𝐭, _, _, _, _, r => r
  | A ⇒ B, S, _, b, _, r =>
      .trans (.eta r.1 (Fset.subset_notMem (supp_deriv r.1) (Fset.new_notMem S)))
        (lam' (Fset.new_notMem S)
          (glueReify (A := B)
            (castGlue (congrArg (fun t => t ∙ (𝐯(Fset.new S) : Tm0)) (rnUnit b))
              (r.2 (RnHom.proj A (Fset.new_notMem S))
                (reflectEl (.var .new)) (glueReflect (.var .new))))))

/-- Agda: `⟦↑⟧` (GST/LogicalRelation.agda). -/
def glueReflect : {A : Ty} → {S : Fset} → {Γ : Cx S} → {a : Tm0} →
    (q : Γ ⊢ᵘ a ∶ A) → Glue Γ a A (reflectEl q)
  | 𝐍𝐚𝐭, _, _, _, q => .refl (neDeriv q)
  | _ ⇒ B, _, _, _, q =>
      ⟨neDeriv q, fun p 𝓪 r =>
        glueCong B _ _
          (glueReflect (.app (rnNe p.pf q) (reifyNf 𝓪)))
          (.app (.refl (rnDeriv p.pf (neDeriv q))) (glueReify r))
          (((𝓓 B).obj _).rfl' _)⟩

end

/-! ## Naturality -/

/-- Agda: `⟦ntl⟧` (GST/LogicalRelation.agda). -/
def glueNtl : {A : Ty} → {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {a : Tm0} →
    {𝓪 : Psh.El (𝓓 A) Γ} → Glue Γ a A 𝓪 → (p : RnHom Γ' Γ) →
    Glue Γ' (p.rn * a) A (((𝓓 A).act p).map 𝓪)
  | 𝐍𝐚𝐭, _, _, _, _, _, _, q, p => rnConv p.pf q
  | _ ⇒ B, _, _, _, _, a, _, q, p =>
      ⟨rnDeriv p.pf q.1, fun p' 𝓪 r =>
        glueCong B _ _ (q.2 (p ∘ᵣ p') 𝓪 r)
          (castEq rfl (congrArg (fun t => t ∙ _) (rnAssoc p.rn p'.rn a).symm)
            (.refl (.app (rnDeriv p'.pf (rnDeriv p.pf q.1)) (glueEsc r))))
          (((𝓓 B).obj _).rfl' _)⟩

/-- Agda: `⟦ntlˢ⟧` (GST/LogicalRelation.agda). -/
def glueNtlSb : {S S' S'' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {Γ'' : Cx S''} →
    {σ : Sb sig} → {𝓼 : Psh.El (𝓔 Γ) Γ'} → GlueSb Γ' σ Γ 𝓼 → (p : RnHom Γ'' Γ') →
    GlueSb Γ'' ((Sb.ofRn p.rn : Sb sig) ∘ˢ σ) Γ (((𝓔 Γ).act p).map 𝓼)
  | _, _, _, .nil, _, _, _, _, _, _ => ⟨⟩
  | _, _, _, .snoc _ _ _ _, _, _, _, _, r, p => ⟨glueNtlSb r.1 p, glueNtl r.2 p⟩

/-! ## The fundamental property -/

/-- Agda: `FPVar` (GST/LogicalRelation.agda). -/
def FPVar : {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {σ : Sb sig} → {A : Ty} →
    {x : Atom} → {𝓼 : Psh.El (𝓔 Γ) Γ'} → (q : (x, A) isIn Γ) → GlueSb Γ' σ Γ 𝓼 →
    Glue Γ' (σ x) A ((val q).hom.map 𝓼)
  | _, _, _, _, _, _, _, _, .new, r => r.2
  | _, _, _, _, _, _, _, _, .old q, r => FPVar q r.1

/-- Agda: `FPNrec` (GST/LogicalRelation.agda). -/
def FPNrec {C : Ty} {S : Fset} {Γ : Cx S} {c₀ cs a : Tm0} (𝓬₀ : Psh.El (𝓓 C) Γ)
    (𝓬s : Psh.El (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)) Γ) (r₀ : Glue Γ c₀ C 𝓬₀)
    (r₁ : Glue Γ cs (𝐍𝐚𝐭 ⇒ C ⇒ C) 𝓬s) :
    {n : Tm0} → (q : Γ ⊢ⁿ n ∶ 𝐍𝐚𝐭) → (Γ ⊢ a ＝ n ∶ 𝐍𝐚𝐭) →
      Glue Γ (𝐧𝐫𝐞𝐜 c₀ cs a) C (nrecSem 𝓬₀ 𝓬s q)
  | _, .zero, q₂ =>
      glueCong C 𝓬₀ 𝓬₀ r₀
        (.trans (.nrec (.refl (glueEsc r₀)) (.refl r₁.1) q₂)
          (.betaZero (glueEsc r₀) r₁.1))
        (((𝓓 C).obj Γ).rfl' 𝓬₀)
  | _, .succ q, q₂ =>
      glueCong C _ _
        ((r₁.2 (RnHom.id Γ) ⟨_, q⟩ (.refl (nfDeriv q))).2 (RnHom.id Γ)
          (nrecSem 𝓬₀ 𝓬s q) (FPNrec 𝓬₀ 𝓬s r₀ r₁ q (.refl (nfDeriv q))))
        (castEq rfl
          (by
            show (cs ∙ _) ∙ 𝐧𝐫𝐞𝐜 c₀ cs _
                = (Rn.id * ((Rn.id * cs) ∙ _)) ∙ 𝐧𝐫𝐞𝐜 c₀ cs _
            rw [rnUnit, rnUnit])
          (.trans (.nrec (.refl (glueEsc r₀)) (.refl r₁.1) q₂)
            (.betaSucc (glueEsc r₀) r₁.1 (nfDeriv q))))
        (((𝓓 C).obj Γ).rfl' _)
  | _, .neu q, q₂ =>
      glueCong C _ _ (glueReflect (.nrec (reifyNf 𝓬₀) (reifyNf 𝓬s) q))
        (.nrec (glueReify r₀) (glueReify (A := 𝐍𝐚𝐭 ⇒ C ⇒ C) r₁) q₂)
        (((𝓓 C).obj Γ).rfl' _)

/-- Agda: `FP` (GST/LogicalRelation.agda). -/
def FP : {S : Fset} → {Γ : Cx S} → {A : Ty} → {a : Tm0} → (q : Γ ⊢ a ∶ A) →
    {S' : Fset} → {Γ' : Cx S'} → {σ : Sb sig} → {𝓼 : Psh.El (𝓔 Γ) Γ'} →
    GlueSb Γ' σ Γ 𝓼 → Glue Γ' (σ * a) A (sem₀ q 𝓼)
  | _, _, _, _, .var (x := x) q₁, _, _, σ, _, r =>
      castGlue (Trm.weaken_self (σ x) (Nat.zero_le 0)).symm (FPVar q₁ r)
  | _, Γ, _, _, .lam (A := A) (B := B) (b := b) (x := x) (h := hx) q₀ hb,
      _, Γ', σ, 𝓼, r =>
      let f := fresh (((σ * b, b), dom Γ') : (Tm 1 × Tm 1) × Fset)
      have hσb : f.val # σ * b :=
        Fset.notMem_union_left (Fset.notMem_union_left f.property)
      have hΓ' : f.val ∉ᶠ dom Γ' := Fset.notMem_union_right f.property
      have rlam : Γ' ⊢ 𝛌 A (σ * b) ∶ A ⇒ B :=
        .lam (h := hΓ') (sbDerivBody hx hΓ' b (glueEscSb r) q₀ hb) hσb
      ⟨rlam, fun {_} {Γ''} {a'} p 𝓪 r' =>
        glueCong B _ _
          (FP q₀
            (show GlueSb Γ'' (((Sb.ofRn p.rn : Sb sig) ∘ˢ σ) ∘/ x ≔ a')
                (Γ ⨟ x ∶ A ∣ hx) (((𝓔 Γ).act p).map 𝓼, 𝓪) from
              ⟨glueCongSb _ _ (glueNtlSb r p)
                  (sbTypingUpdateFresh hx (rnSb p.pf (glueEscSb r)) (glueEsc r'))
                  (((𝓔 Γ).obj Γ'').rfl' (((𝓔 Γ).act p).map 𝓼)),
                castGlue (Sb.update_eq ((Sb.ofRn p.rn : Sb sig) ∘ˢ σ) x a').symm r'⟩))
          (castEq rfl
            (by
              rw [sbUpdate_conc ((Sb.ofRn p.rn : Sb sig) ∘ˢ σ) x a' b hb,
                sbAssoc σ (Sb.ofRn p.rn) b]
              rfl)
            (betaLam' (rnDeriv p.pf rlam) (glueEsc r') rfl))
          (((𝓓 B).obj Γ'').rfl' _)⟩
  | _, _, _, _, .app (b := b) q₀ q₁, _, Γ', σ, 𝓼, r =>
      castGlue (congrArg (fun t => t ∙ (σ * _)) (rnUnit (σ * b)))
        ((FP q₀ r).2 (RnHom.id Γ') (sem₀ q₁ 𝓼) (FP q₁ r))
  | _, _, _, _, .zero, _, _, _, _, _ => .refl .zero
  | _, _, _, _, .succ q, _, _, _, _, r => .succ (FP q r)
  | _, _, _, _, .nrec q₀ q₁ q₂, _, _, _, 𝓼, r =>
      FPNrec (sem₀ q₀ 𝓼) (sem₀ q₁ 𝓼) (FP q₀ r) (FP q₁ r) (sem₀ q₂ 𝓼).pf (FP q₂ r)

/-- Agda: `FPˢ` (GST/LogicalRelation.agda). -/
def FPSb : {S S' S'' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {Γ'' : Cx S''} →
    {σ σ' : Sb sig} → {𝓼 : Psh.El (𝓔 Γ') Γ''} → (q : Γ' ⊢ˢ σ ∶ Γ) →
    GlueSb Γ'' σ' Γ' 𝓼 → GlueSb Γ'' (σ' ∘ˢ σ) Γ (semSb₀ q 𝓼)
  | _, _, _, .nil, _, _, _, _, _, .nil, _ => ⟨⟩
  | _, _, _, .snoc _ _ _ _, _, _, _, _, _, .snoc q₀ q₁, r =>
      ⟨FPSb q₀ r, FP q₁ r⟩

/-- Agda: `FPˢ₀` (GST/LogicalRelation.agda). -/
def FPSb₀ : {S : Fset} → (Γ : Cx S) → GlueSb Γ (Sb.id : Sb sig) Γ (env₀ Γ)
  | _, .nil => ⟨⟩
  | _, .snoc Γ _ A h => ⟨glueNtlSb (FPSb₀ Γ) (RnHom.proj A h), glueReflect (.var .new)⟩

end GST

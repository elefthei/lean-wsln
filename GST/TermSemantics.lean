import GST.ReifyReflect

/-!
# Presheaf semantics of terms

Port of `agda-code/agda/GST/TermSemantics.agda`.

A *derivation* `q : Γ ⊢ a ∶ A` is interpreted as a natural transformation
`sem q : Psh.Hom (𝓔 Γ) (𝓓 A)`; `sem₀ q 𝓼` is its value at an environment.  Because
the interpretation is defined on derivations rather than on terms, the bulk of the
file is the coherence properties Agda also has to prove: `rnSem` (renaming),
`irrelSem` (independence of the derivation), `rnSemBody` (independence of the
concreting atom), `wkSem`, `sbSem` (substitution) and `concSem`.

Two Lean-specific points.

* Agda's `nrec₁` recurses on a normal form *of type `𝐍𝐚𝐭`*.  A Lean structural
  recursion needs the indices of the family to be variables, so the recursion is on a
  normal form of an arbitrary type `A` carrying `A = 𝐍𝐚𝐭` (`nrecSemAux`); `nrecSem`
  instantiates it.  This keeps the defining equations definitional.
* Agda's `rnSem` carries an explicit equation `A ≡ A'` between the two types and a
  `subst` in the conclusion.  Here the two derivations are given the *same* type
  index: dependent pattern matching refines it in the λ-case exactly as Agda's `⇒inj`
  does, so both the equation and the transport are unnecessary.
-/

namespace GST

open WSLN

/-! ## Semantic `natrec` -/

/-- Recursor semantics on a normal form of an arbitrary type together with the evidence that
the type is `𝐍𝐚𝐭`; see the module docstring. -/
def nrecSemAux {C : Ty} {S : Fset} {Γ : Cx S} (𝓬₀ : Psh.El (𝓓 C) Γ)
    (𝓬s : Psh.El (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)) Γ) :
    {n : Tm0} → {A : Ty} → (Γ ⊢ⁿ n ∶ A) → A = 𝐍𝐚𝐭 → Psh.El (𝓓 C) Γ
  | _, _, .lam _ _, e => absurd e (by intro h; cases h)
  | _, _, .zero, _ => 𝓬₀
  | _, _, .succ q, _ =>
      Psh.ev.hom.map (Psh.ev.hom.map (𝓬s, ⟨_, q⟩), nrecSemAux 𝓬₀ 𝓬s q rfl)
  | _, _, .neu q, e => reflectEl (.nrec (reifyNf 𝓬₀) (reifyNf 𝓬s) (e ▸ q))

def nrecSem {C : Ty} {S : Fset} {Γ : Cx S} (𝓬₀ : Psh.El (𝓓 C) Γ)
    (𝓬s : Psh.El (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)) Γ) {n : Tm0} (q : Γ ⊢ⁿ n ∶ 𝐍𝐚𝐭) :
    Psh.El (𝓓 C) Γ := nrecSemAux 𝓬₀ 𝓬s q rfl

theorem evResp {A B : Ty} {S : Fset} {Γ : Cx S} {𝓯 𝓯' : Psh.El (𝓓 (A ⇒ B)) Γ}
    {𝓪 𝓪' : Psh.El (𝓓 A) Γ} (e : (𝓓 (A ⇒ B)).obj Γ ∋ 𝓯 ~ 𝓯')
    (e' : (𝓓 A).obj Γ ∋ 𝓪 ~ 𝓪') :
    (𝓓 B).obj Γ ∋ Psh.ev.hom.map (𝓯, 𝓪) ~ Psh.ev.hom.map (𝓯', 𝓪') :=
  (Psh.ev (A := 𝓓 A) (B := 𝓓 B)).hom.resp ⟨e, e'⟩

/-- The recursor semantics respects the relation, for two derivations of one numeral. -/
theorem nrecSem₂ {C : Ty} {S : Fset} {Γ : Cx S} {𝓬₀ 𝓬₀' : Psh.El (𝓓 C) Γ}
    {𝓬s 𝓬s' : Psh.El (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)) Γ} (e₀ : (𝓓 C).obj Γ ∋ 𝓬₀ ~ 𝓬₀')
    (e₁ : (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)).obj Γ ∋ 𝓬s ~ 𝓬s') : {n : Tm0} → (q q' : Γ ⊢ⁿ n ∶ 𝐍𝐚𝐭) →
      (𝓓 C).obj Γ ∋ nrecSem 𝓬₀ 𝓬s q ~ nrecSem 𝓬₀' 𝓬s' q'
  | _, .zero, .zero => e₀
  | _, .succ q, .succ q' =>
      evResp (A := C) (B := C)
        (evResp (A := 𝐍𝐚𝐭) (B := C ⇒ C) (𝓪 := ⟨_, q⟩) (𝓪' := ⟨_, q'⟩) e₁ rfl)
        (nrecSem₂ e₀ e₁ q q')
  | _, .neu q, .neu q' => by
      refine (reflect C).hom.resp ?_
      show 𝐧𝐫𝐞𝐜 (reifyTm C 𝓬₀) (reifyTm (𝐍𝐚𝐭 ⇒ C ⇒ C) 𝓬s) _
          = 𝐧𝐫𝐞𝐜 (reifyTm C 𝓬₀') (reifyTm (𝐍𝐚𝐭 ⇒ C ⇒ C) 𝓬s') _
      have h₀ : reifyTm C 𝓬₀ = reifyTm C 𝓬₀' := (reify C).hom.resp e₀
      have h₁ : reifyTm (𝐍𝐚𝐭 ⇒ C ⇒ C) 𝓬s = reifyTm (𝐍𝐚𝐭 ⇒ C ⇒ C) 𝓬s' :=
        (reify (𝐍𝐚𝐭 ⇒ C ⇒ C)).hom.resp e₁
      rw [h₀, h₁]

/-- The recursor semantics respects the relation, for numerals related in the setoid of normal
forms rather than being literally the same term. -/
theorem nrecSem₂' {C : Ty} {S : Fset} {Γ : Cx S} {𝓬₀ 𝓬₀' : Psh.El (𝓓 C) Γ}
    {𝓬s 𝓬s' : Psh.El (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)) Γ} {n n' : Tm0} (q : Γ ⊢ⁿ n ∶ 𝐍𝐚𝐭)
    (q' : Γ ⊢ⁿ n' ∶ 𝐍𝐚𝐭) (e₀ : (𝓓 C).obj Γ ∋ 𝓬₀ ~ 𝓬₀')
    (e₁ : (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)).obj Γ ∋ 𝓬s ~ 𝓬s') (e₂ : n = n') :
    (𝓓 C).obj Γ ∋ nrecSem 𝓬₀ 𝓬s q ~ nrecSem 𝓬₀' 𝓬s' q' := by
  cases e₂; exact nrecSem₂ e₀ e₁ q q'

theorem nrecSem₃ {C : Ty} {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'}
    (𝓬₀ : Psh.El (𝓓 C) Γ) (𝓬s : Psh.El (𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)) Γ) (p : RnHom Γ' Γ) :
    {n : Tm0} → (q : Γ ⊢ⁿ n ∶ 𝐍𝐚𝐭) →
      (𝓓 C).obj Γ' ∋
        nrecSem (((𝓓 C).act p).map 𝓬₀) (((𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)).act p).map 𝓬s)
          (rnNf p.pf q) ~ ((𝓓 C).act p).map (nrecSem 𝓬₀ 𝓬s q)
  | _, .zero => ((𝓓 C).obj Γ').rfl' (((𝓓 C).act p).map 𝓬₀)
  | _, .succ q =>
      ((𝓓 C).obj Γ').trans'
        (evResp (A := C) (B := C)
          ((Psh.ev (A := 𝓓 𝐍𝐚𝐭) (B := 𝓓 (C ⇒ C))).ntl p (𝓬s, ⟨_, q⟩))
          (nrecSem₃ 𝓬₀ 𝓬s p q))
        ((Psh.ev (A := 𝓓 C) (B := 𝓓 C)).ntl p
          (Psh.ev.hom.map (𝓬s, ⟨_, q⟩), nrecSem 𝓬₀ 𝓬s q))
  | _, .neu q => by
      refine ((𝓓 C).obj Γ').trans' ((reflect C).hom.resp ?_)
        ((reflect C).ntl p ⟨_, Ne.nrec (reifyNf 𝓬₀) (reifyNf 𝓬s) q⟩)
      have h₀ : reifyTm C (((𝓓 C).act p).map 𝓬₀) = p.rn * reifyTm C 𝓬₀ :=
        (reify C).ntl p 𝓬₀
      have h₁ : reifyTm (𝐍𝐚𝐭 ⇒ C ⇒ C) (((𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)).act p).map 𝓬s)
          = p.rn * reifyTm (𝐍𝐚𝐭 ⇒ C ⇒ C) 𝓬s := (reify (𝐍𝐚𝐭 ⇒ C ⇒ C)).ntl p 𝓬s
      show 𝐧𝐫𝐞𝐜 (reifyTm C (((𝓓 C).act p).map 𝓬₀))
            (reifyTm (𝐍𝐚𝐭 ⇒ C ⇒ C) (((𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C)).act p).map 𝓬s)) _
          = p.rn * 𝐧𝐫𝐞𝐜 (reifyTm C 𝓬₀) (reifyTm (𝐍𝐚𝐭 ⇒ C ⇒ C) 𝓬s) _
      rw [h₀, h₁]
      rfl

/-! ## The interpretations of the operators -/

def zeroSem {S : Fset} {Γ : Cx S} : Psh.Hom (𝓔 Γ) (Norm 𝐍𝐚𝐭) where
  hom := { map := fun _ => ⟨𝐳𝐞𝐫𝐨, .zero⟩, resp := fun _ => rfl }
  ntl _ _ := rfl

def succSem : Psh.Hom (Norm 𝐍𝐚𝐭) (Norm 𝐍𝐚𝐭) where
  hom :=
    { map := fun a => ⟨𝐬𝐮𝐜𝐜 a.nt, .succ a.pf⟩
      resp := fun e => congrArg (fun t => 𝐬𝐮𝐜𝐜 t) e }
  ntl _ _ := rfl

def nrecHom {C : Ty} : Psh.Hom (𝓓 C ×^ 𝓓 (𝐍𝐚𝐭 ⇒ C ⇒ C) ×^ 𝓓 𝐍𝐚𝐭) (𝓓 C) where
  hom :=
    { map := fun z => nrecSem z.1.1 z.1.2 z.2.pf
      resp := fun {u v} e => nrecSem₂' u.2.pf v.2.pf e.1.1 e.1.2 e.2 }
  ntl p z := nrecSem₃ z.1.1 z.1.2 p z.2.pf

/-! ## The interpretation of a derivation -/

def sem {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} : (Γ ⊢ a ∶ A) → Psh.Hom (𝓔 Γ) (𝓓 A)
  | .var q => val q
  | .lam q _ => Psh.cur (sem q)
  | .app q₀ q₁ => Psh.ev.comp (Psh.pair (sem q₀) (sem q₁))
  | .zero => zeroSem
  | .succ q => succSem.comp (sem q)
  | .nrec q₀ q₁ q₂ =>
      nrecHom.comp (Psh.pair (Psh.pair (sem q₀) (sem q₁)) (sem q₂))

def sem₀ {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {A : Ty} {a : Tm0} (q : Γ ⊢ a ∶ A)
    (𝓼 : Psh.El (𝓔 Γ) Γ') : Psh.El (𝓓 A) Γ' := (sem q).hom.map 𝓼

/-! ## Semantics of renaming -/

theorem rnSem {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} (q : Γ ⊢ a ∶ A) :
    ∀ {S' S'' : Fset} {Γ' : Cx S'} {Γ'' : Cx S''} (p : RnHom Γ' Γ)
      (𝓼 : Psh.El (𝓔 Γ') Γ'') {a' : Tm0} (q' : Γ' ⊢ a' ∶ A), p.rn * a = a' →
      (𝓓 A).obj Γ'' ∋ sem₀ q' 𝓼 ~ sem₀ q (p ⊚ 𝓼) := by
  induction q with
  | var q₁ =>
      intro _ _ _ _ p 𝓼 _ q' e
      cases e
      cases q' with
      | var q₁' => exact renVal p 𝓼 q₁ q₁'
  | @lam _ Γ₁ A B b x hx q₀ hb ih =>
      intro _ _ Γ' _ p 𝓼 _ q' e
      cases e
      cases q' with
      | @lam _ _ _ _ _ x' hx' q₀' hb' =>
          intro _ Γ''' z
          refine ((𝓓 B).obj Γ''').trans'
            (ih (liftRnHom p x x' A hx hx') (((𝓔 Γ').act z.1).map 𝓼, z.2) q₀'
              (rnUpdate_conc p.rn x x' b hb)) ?_
          exact (sem q₀).hom.resp
            (show (𝓔 (Γ₁ ⨟ x ∶ A ∣ hx)).obj Γ''' ∋
                liftRnHom p x x' A hx hx' ⊚ (((𝓔 Γ').act z.1).map 𝓼, z.2) ~
                  (((𝓔 Γ₁).act z.1).map (p ⊚ 𝓼), z.2) from
              ((𝓔 (Γ₁ ⨟ x ∶ A ∣ hx)).obj Γ''').trans'
                (renUpdate hx hx' p (((𝓔 Γ').act z.1).map 𝓼) z.2)
                ⟨envComp_ntl p z.1 𝓼, ((𝓓 A).obj Γ''').rfl' z.2⟩)
  | @app _ _ A₁ _ _ _ q₀ q₁ ih₀ ih₁ =>
      intro _ _ _ _ p 𝓼 _ q' e
      cases e
      cases q' with
      | @app _ _ A₂ _ _ _ q₀' q₁' =>
          cases svTy q₁' (rnDeriv p.pf q₁)
          exact evResp (A := A₁) (ih₀ p 𝓼 q₀' rfl) (ih₁ p 𝓼 q₁' rfl)
  | zero =>
      intro _ _ _ _ p 𝓼 _ q' e
      cases e
      cases q' with
      | zero => rfl
  | succ q ih =>
      intro _ _ _ _ p 𝓼 _ q' e
      cases e
      cases q' with
      | succ q' => exact congrArg (fun t => 𝐬𝐮𝐜𝐜 t) (ih p 𝓼 q' rfl)
  | nrec q₀ q₁ q₂ ih₀ ih₁ ih₂ =>
      intro _ _ _ _ p 𝓼 _ q' e
      cases e
      cases q' with
      | nrec q₀' q₁' q₂' =>
          exact nrecSem₂' (sem₀ q₂' 𝓼).pf (sem₀ q₂ (p ⊚ 𝓼)).pf
            (ih₀ p 𝓼 q₀' rfl) (ih₁ p 𝓼 q₁' rfl) (ih₂ p 𝓼 q₂' rfl)

theorem semRn {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''} {A : Ty}
    {a : Tm0} (p : RnHom Γ' Γ) (𝓼 : Psh.El (𝓔 Γ') Γ'') (q : Γ ⊢ a ∶ A) :
    (𝓓 A).obj Γ'' ∋ sem₀ (rnDeriv p.pf q) 𝓼 ~ sem₀ q (p ⊚ 𝓼) :=
  rnSem q p 𝓼 (rnDeriv p.pf q) rfl

/-- The semantics of a term does not depend on the derivation. -/
theorem irrelSem {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {A : Ty} {a a' : Tm0}
    (q : Γ ⊢ a ∶ A) (q' : Γ ⊢ a' ∶ A) (e : a = a') (𝓼 : Psh.El (𝓔 Γ) Γ') :
    (𝓓 A).obj Γ' ∋ sem₀ q 𝓼 ~ sem₀ q' 𝓼 := by
  cases e
  have h := rnSem q' (RnHom.id Γ) 𝓼 q (rnUnit a)
  rw [envComp_unit 𝓼] at h
  exact h

/-- The semantics of an abstraction does not depend on the atom at which it is concreted. -/
theorem rnSemBody {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {A B : Ty} {x x' : Atom}
    (hx : x ∉ᶠ S) (hx' : x' ∉ᶠ S) (b : Tm 1) (q : (Γ ⨟ x ∶ A ∣ hx) ⊢ b[x] ∶ B)
    (q' : (Γ ⨟ x' ∶ A ∣ hx') ⊢ b[x'] ∶ B) (_ : x # b) (hb' : x' # b)
    (𝓼 : Psh.El (𝓔 Γ) Γ') (𝓪 : Psh.El (𝓓 A) Γ') :
    (𝓓 B).obj Γ' ∋ sem₀ q (𝓼, 𝓪) ~ sem₀ q' (𝓼, 𝓪) := by
  have 𝓮 : (𝓔 (Γ ⨟ x' ∶ A ∣ hx')).obj Γ' ∋
      liftRnHom (RnHom.id Γ) x' x A hx' hx ⊚ (𝓼, 𝓪) ~ (𝓼, 𝓪) := by
    have h := renUpdate hx' hx (RnHom.id Γ) 𝓼 𝓪
    rw [envComp_unit 𝓼] at h
    exact h
  exact ((𝓓 B).obj Γ').trans'
    (rnSem q' (liftRnHom (RnHom.id Γ) x' x A hx' hx) (𝓼, 𝓪) q
      (srn_conc x' x b hb'))
    ((sem q').hom.resp 𝓮)

/-! ## Semantics of weakening -/

theorem wkSem {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {A A' : Ty} {a : Tm0} {x : Atom}
    (h : x ∉ᶠ S) (q : Γ ⊢ a ∶ A) (q' : (Γ ⨟ x ∶ A' ∣ h) ⊢ a ∶ A)
    (𝓼 : Psh.El (𝓔 Γ) Γ') (𝓪 : Psh.El (𝓓 A') Γ') :
    (𝓓 A).obj Γ' ∋ sem₀ q' (𝓼, 𝓪) ~ sem₀ q 𝓼 := by
  have h₀ := rnSem q (wkRnHom (RnHom.id Γ) A' h) (𝓼, 𝓪) q' (rnUnit a)
  rw [renWk (RnHom.id Γ) A' 𝓼 𝓪, envComp_unit 𝓼] at h₀
  exact h₀

/-! ## Semantics of substitution -/

def semSb {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {σ : Sb sig} :
    (Γ' ⊢ˢ σ ∶ Γ) → Psh.Hom (𝓔 Γ') (𝓔 Γ)
  | .nil => Psh.bang
  | .snoc q₀ q₁ => Psh.pair (semSb q₀) (sem q₁)

def semSb₀ {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''} {σ : Sb sig}
    (q : Γ' ⊢ˢ σ ∶ Γ) (𝓼 : Psh.El (𝓔 Γ') Γ'') : Psh.El (𝓔 Γ) Γ'' :=
  (semSb q).hom.map 𝓼

theorem irrelSemSb : {S S' S'' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {Γ'' : Cx S''} →
    {σ σ' : Sb sig} → (q : Γ' ⊢ˢ σ ∶ Γ) → (q' : Γ' ⊢ˢ σ' ∶ Γ) →
    (sbSetd (dom Γ) ∋ σ ~ σ') → (𝓼 : Psh.El (𝓔 Γ') Γ'') →
    (𝓔 Γ).obj Γ'' ∋ semSb₀ q 𝓼 ~ semSb₀ q' 𝓼
  | _, _, _, .nil, _, _, _, _, .nil, .nil, _, _ => trivial
  | _, _, _, .snoc _ x _ _, _, _, _, _, .snoc q₀ q₁, .snoc q₀' q₁', e, 𝓼 =>
      ⟨irrelSemSb q₀ q₀' (fun y r => e y (.unionL r)) 𝓼,
       irrelSem q₁ q₁' (e x (.unionR .single)) 𝓼⟩

theorem rnSemSb : {S S' S'' S''' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} →
    {Γ'' : Cx S''} → {Γ''' : Cx S'''} → {σ σ' : Sb sig} → (p : RnHom Γ'' Γ') →
    (𝓼 : Psh.El (𝓔 Γ'') Γ''') → (q : Γ' ⊢ˢ σ ∶ Γ) → (q' : Γ'' ⊢ˢ σ' ∶ Γ) →
    (sbSetd (dom Γ) ∋ ((Sb.ofRn p.rn : Sb sig) ∘ˢ σ) ~ σ') →
    (𝓔 Γ).obj Γ''' ∋ semSb₀ q' 𝓼 ~ semSb₀ q (p ⊚ 𝓼)
  | _, _, _, _, .nil, _, _, _, _, _, _, _, .nil, .nil, _ => trivial
  | _, _, _, _, .snoc _ x _ _, _, _, _, _, _, p, 𝓼, .snoc q₀ q₁, .snoc q₀' q₁', e =>
      ⟨rnSemSb p 𝓼 q₀ q₀' (fun y r => e y (.unionL r)),
       rnSem q₁ p 𝓼 q₁' (e x (.unionR .single))⟩

theorem wkSemSb {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''} {σ : Sb sig}
    {A : Ty} {x : Atom} (h : x ∉ᶠ S') (q : Γ' ⊢ˢ σ ∶ Γ)
    (𝓼 : Psh.El (𝓔 Γ') Γ'') (𝓪 : Psh.El (𝓓 A) Γ'') :
    (𝓔 Γ).obj Γ'' ∋ semSb₀ (wkSb (A := A) h q) (𝓼, 𝓪) ~ semSb₀ q 𝓼 := by
  have h₀ := rnSemSb (wkRnHom (RnHom.id Γ') A h) (𝓼, 𝓪) q (wkSb (A := A) h q)
    (fun y _ => sbUnit (σ y))
  rw [renWk (RnHom.id Γ') A 𝓼 𝓪, envComp_unit 𝓼] at h₀
  exact h₀

theorem semSbUnit : {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} →
    (𝓼 : Psh.El (𝓔 Γ) Γ') → (𝓔 Γ).obj Γ' ∋ semSb₀ (sbTypingId Γ) 𝓼 ~ 𝓼
  | _, _, .nil, _, _ => trivial
  | _, _, .snoc Γ _ A h, Γ', 𝓼 =>
      ⟨((𝓔 Γ).obj Γ').trans' (wkSemSb h (sbTypingId Γ) 𝓼.1 𝓼.2)
        (semSbUnit 𝓼.1), ((𝓓 A).obj Γ').rfl' 𝓼.2⟩

theorem sbSemVar : {S S' S'' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {Γ'' : Cx S''} →
    {σ : Sb sig} → {A : Ty} → {x : Atom} → (q : Γ' ⊢ˢ σ ∶ Γ) → (q' : (x, A) isIn Γ) →
    (𝓼 : Psh.El (𝓔 Γ') Γ'') →
    (𝓓 A).obj Γ'' ∋ sem₀ (sbVar q' q) 𝓼 ~ (val q').hom.map (semSb₀ q 𝓼)
  | _, _, _, _, _, _, _, _, _, .snoc _ q₁, .new, 𝓼 =>
      ((𝓓 _).obj _).rfl' (sem₀ q₁ 𝓼)
  | _, _, _, _, _, _, _, _, _, .snoc q₀ _, .old q', 𝓼 => sbSemVar q₀ q' 𝓼

theorem sbSemLift {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''}
    {σ : Sb sig} {A : Ty} {x x' : Atom} (hx : x ∉ᶠ S) (hx' : x' ∉ᶠ S')
    (q : Γ' ⊢ˢ σ ∶ Γ) (q' : (Γ' ⨟ x' ∶ A ∣ hx') ⊢ˢ (σ ∘/ x ≔ 𝐯x') ∶ (Γ ⨟ x ∶ A ∣ hx))
    (𝓼 : Psh.El (𝓔 Γ') Γ'') (𝓪 : Psh.El (𝓓 A) Γ'') :
    (𝓔 (Γ ⨟ x ∶ A ∣ hx)).obj Γ'' ∋ semSb₀ q' (𝓼, 𝓪) ~ (semSb₀ q 𝓼, 𝓪) :=
  ((𝓔 (Γ ⨟ x ∶ A ∣ hx)).obj Γ'').trans'
    (irrelSemSb q' (liftSb hx hx' q) (fun _ _ => rfl) (𝓼, 𝓪))
    ⟨((𝓔 Γ).obj Γ'').trans'
        (irrelSemSb (sbTypingExt (sbUpdate_fresh σ hx) (wkSb (A := A) hx' q))
          (wkSb (A := A) hx' q)
          ((sbSetd (dom Γ)).symm' (sbUpdate_fresh σ hx)) (𝓼, 𝓪))
        (wkSemSb (A := A) hx' q 𝓼 𝓪),
      irrelSem (Γ := Γ' ⨟ x' ∶ A ∣ hx')
        (castTm (Sb.update_eq σ x (𝐯x')).symm (.var .new)) (.var .new)
        (Sb.update_eq σ x (𝐯x')) (𝓼, 𝓪)⟩

theorem sbSem {S : Fset} {Γ : Cx S} {A : Ty} {a : Tm0} (q : Γ ⊢ a ∶ A) :
    ∀ {S' S'' : Fset} {Γ' : Cx S'} {Γ'' : Cx S''} {σ : Sb sig} (p : Γ' ⊢ˢ σ ∶ Γ)
      (𝓼 : Psh.El (𝓔 Γ') Γ''),
      (𝓓 A).obj Γ'' ∋ sem₀ (sbDeriv p q) 𝓼 ~ sem₀ q (semSb₀ p 𝓼) := by
  induction q with
  | @var _ _ A x q₁ =>
      intro _ _ _ _ σ p 𝓼
      exact ((𝓓 A).obj _).trans'
        (irrelSem (castTm (Trm.weaken_self (σ x) (Nat.zero_le 0)).symm (sbVar q₁ p))
          (sbVar q₁ p) (Trm.weaken_self (σ x) (Nat.zero_le 0)) 𝓼)
        (sbSemVar p q₁ 𝓼)
  | @lam _ _ A B b x hx q₀ hb ih =>
      intro _ _ Γ' Γ'' σ p 𝓼 _ Γ''' z
      let f := freshFor (σ * b) (dom Γ')
      have hΓ' : f.val ∉ᶠ dom Γ' := f.property.2
      refine ((𝓓 B).obj Γ''').trans'
        (irrelSem
          (castTm (sbUpdate_conc σ x (𝐯f.val) b hb)
            (sbDeriv (liftSb hx hΓ' p) q₀))
          (sbDeriv (liftSb hx hΓ' p) q₀)
          (sbUpdate_conc σ x (𝐯f.val) b hb).symm
          (((𝓔 Γ').act z.1).map 𝓼, z.2)) ?_
      refine ((𝓓 B).obj Γ''').trans'
        (ih (liftSb hx hΓ' p) (((𝓔 Γ').act z.1).map 𝓼, z.2)) ?_
      refine ((𝓓 B).obj Γ''').trans'
        ((sem q₀).hom.resp
          (sbSemLift hx hΓ' p (liftSb hx hΓ' p) (((𝓔 Γ').act z.1).map 𝓼) z.2)) ?_
      exact (sem q₀).hom.resp
        ⟨(semSb p).ntl z.1 𝓼, ((𝓓 A).obj Γ''').rfl' z.2⟩
  | @app _ _ A₁ _ _ _ q₀ q₁ ih₀ ih₁ =>
      intro _ _ _ _ _ p 𝓼
      exact evResp (A := A₁) (ih₀ p 𝓼) (ih₁ p 𝓼)
  | zero => intro _ _ _ _ _ _ _; rfl
  | succ q ih =>
      intro _ _ _ _ _ p 𝓼
      exact congrArg (fun t => 𝐬𝐮𝐜𝐜 t) (ih p 𝓼)
  | nrec q₀ q₁ q₂ ih₀ ih₁ ih₂ =>
      intro _ _ _ _ _ p 𝓼
      exact nrecSem₂' (sem₀ (sbDeriv p q₂) 𝓼).pf (sem₀ q₂ (semSb₀ p 𝓼)).pf
        (ih₀ p 𝓼) (ih₁ p 𝓼) (ih₂ p 𝓼)

/-! ## Semantics of concretion -/

theorem concSem {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {A B : Ty} {a : Tm0} (b : Tm 1)
    (x : Atom) (hx : x ∉ᶠ S) (q₀ : (Γ ⨟ x ∶ A ∣ hx) ⊢ b[x] ∶ B) (q₁ : Γ ⊢ a ∶ A)
    (q₂ : Γ ⊢ b[a] ∶ B) (hb : x # b) (𝓼 : Psh.El (𝓔 Γ) Γ') :
    (𝓓 B).obj Γ' ∋ sem₀ q₀ (𝓼, sem₀ q₁ 𝓼) ~ sem₀ q₂ 𝓼 :=
  ((𝓓 B).obj Γ').symm'
    (((𝓓 B).obj Γ').trans'
      (irrelSem q₂ (sbDeriv (sbTypingUpdate hx (sbTypingId Γ) q₁) q₀)
        (ssb_conc x a b hb).symm 𝓼)
      (((𝓓 B).obj Γ').trans'
        (sbSem q₀ (sbTypingUpdate hx (sbTypingId Γ) q₁) 𝓼)
        ((sem q₀).hom.resp
          ⟨((𝓔 Γ).obj Γ').trans'
              (irrelSemSb (sbTypingExt (sbUpdate_fresh Sb.id hx) (sbTypingId Γ))
                (sbTypingId Γ)
                ((sbSetd (dom Γ)).symm' (sbUpdate_fresh Sb.id hx)) 𝓼)
              (semSbUnit 𝓼),
            irrelSem (castTm (Sb.update_eq (Sb.id : Sb sig) x a).symm q₁) q₁
              (Sb.update_eq (Sb.id : Sb sig) x a) 𝓼⟩)))

end GST

import GST.Presheaf
import GST.NormalForm

/-!
# Presheaf semantics of types and contexts

Port of `agda-code/agda/GST/TypeSemantics.agda`.

`Norm A` and `Neut A` are the presheaves of normal and of neutral forms of type `A`,
`tySem A` (Agda `𝓓 A`) is the interpretation of a type and `cxSem Γ` (Agda `𝓔 Γ`) the
presheaf of semantic environments.  The Agda glyphs `𝓓` and `𝓔` are kept as scoped
notation.

The last section is the interaction between environments and renamings: `envComp`
(Agda `_⊚_`) precomposes an environment with a typed renaming.
-/

namespace GST

open WSLN

/-! ## Presheaf of normal forms -/

/-- Agda: `∣Norm∣` (GST/TypeSemantics.agda). -/
structure NormEl {S : Fset} (A : Ty) (Γ : Cx S) : Type where
  /-- Agda: `nt`. The underlying term. -/
  nt : Tm0
  /-- Agda: `pf`. Its normal-form derivation. -/
  pf : Γ ⊢ⁿ nt ∶ A

/-- Agda: `Norm` (GST/TypeSemantics.agda). -/
def Norm (A : Ty) : Psh where
  obj Γ :=
    { El := NormEl A Γ
      rel := fun a a' => a.nt = a'.nt
      rfl' := fun _ => rfl
      symm' := Eq.symm
      trans' := Eq.trans }
  cong := fun {_ _} {_} {_} =>
    { map := fun p =>
        { map := fun a => ⟨p.rn * a.nt, rnNf p.pf a.pf⟩
          resp := fun e => congrArg (fun t => p.rn * t) e }
      resp := fun {p p'} e a =>
        rnRespSupp p.rn p'.rn a.nt fun x r => e x (supp_deriv (nfDeriv a.pf) r) }
  unit _ a := rnUnit a.nt
  assoc p q a := rnAssoc p.rn q.rn a.nt

/-! ## Presheaf of neutral forms -/

/-- Agda: `∣Neut∣` (GST/TypeSemantics.agda). -/
structure NeutEl {S : Fset} (A : Ty) (Γ : Cx S) : Type where
  /-- Agda: `ut`. The underlying term. -/
  ut : Tm0
  /-- Agda: `pf`. Its neutral-form derivation. -/
  pf : Γ ⊢ᵘ ut ∶ A

/-- Agda: `Neut` (GST/TypeSemantics.agda). -/
def Neut (A : Ty) : Psh where
  obj Γ :=
    { El := NeutEl A Γ
      rel := fun a a' => a.ut = a'.ut
      rfl' := fun _ => rfl
      symm' := Eq.symm
      trans' := Eq.trans }
  cong := fun {_ _} {_} {_} =>
    { map := fun p =>
        { map := fun a => ⟨p.rn * a.ut, rnNe p.pf a.pf⟩
          resp := fun e => congrArg (fun t => p.rn * t) e }
      resp := fun {p p'} e a =>
        rnRespSupp p.rn p'.rn a.ut fun x r => e x (supp_deriv (neDeriv a.pf) r) }
  unit _ a := rnUnit a.ut
  assoc p q a := rnAssoc p.rn q.rn a.ut

/-- Agda: `newvar` (GST/TypeSemantics.agda). -/
def newvar {S : Fset} {Γ : Cx S} (x : Atom) (A : Ty) (h : x ∉ᶠ S) :
    Psh.El (Neut A) (Γ ⨟ x ∶ A ∣ h) := ⟨𝐯x, .var .new⟩

/-- Agda: `neu` (GST/TypeSemantics.agda). -/
def neuHom {A : Ty} : Psh.Hom (Neut A) (Norm A) where
  hom := { map := fun a => ⟨a.ut, .neu a.pf⟩, resp := fun e => e }
  ntl _ _ := rfl

/-! ## Presheaf semantics of types -/

/-- Agda: `𝓓` (GST/TypeSemantics.agda). -/
def tySem : Ty → Psh
  | 𝐍𝐚𝐭 => Norm 𝐍𝐚𝐭
  | A ⇒ B => tySem A →^ tySem B

@[inherit_doc tySem] scoped notation:max "𝓓 " A:max => GST.tySem A

/-! ## Presheaf semantics of contexts: semantic environments -/

/-- Agda: `𝓔` (GST/TypeSemantics.agda). -/
def cxSem : {S : Fset} → Cx S → Psh
  | _, .nil => Psh.one
  | _, .snoc Γ _ A _ => cxSem Γ ×^ 𝓓 A

@[inherit_doc cxSem] scoped notation:max "𝓔 " Γ:max => GST.cxSem Γ

/-- Agda: `val` (GST/TypeSemantics.agda). -/
def val : {S : Fset} → {Γ : Cx S} → {A : Ty} → {x : Atom} → ((x, A) isIn Γ) →
    Psh.Hom (𝓔 Γ) (𝓓 A)
  | _, _, _, _, .new =>
      { hom := { map := fun z => z.2, resp := fun e => e.2 }
        ntl := fun p z => ((𝓓 _).obj _).rfl' (((𝓓 _).act p).map z.2) }
  | _, _, _, _, .old q =>
      { hom :=
          { map := fun z => (val q).hom.map z.1
            resp := fun e => (val q).hom.resp e.1 }
        ntl := fun p z => (val q).ntl p z.1 }

/-- Agda: `val₁` (GST/TypeSemantics.agda). -/
theorem val₁ {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {A : Ty} {x x' : Atom}
    {𝓼 𝓼' : Psh.El (𝓔 Γ) Γ'} (q : (x, A) isIn Γ) (q' : (x', A) isIn Γ) (e : x = x')
    (𝓮 : (𝓔 Γ).obj Γ' ∋ 𝓼 ~ 𝓼') :
    (𝓓 A).obj Γ' ∋ (val q).hom.map 𝓼 ~ (val q').hom.map 𝓼' := by
  cases e
  cases IsIn.unique q q'
  exact (val q).hom.resp 𝓮

/-! ## Post-composing a semantic environment with a variable renaming -/

/-- Agda: `_⊚_` (GST/TypeSemantics.agda). -/
def envComp : {S S' S'' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {Γ'' : Cx S''} →
    RnHom Γ' Γ → Psh.El (𝓔 Γ') Γ'' → Psh.El (𝓔 Γ) Γ''
  | _, _, _, .nil, _, _, _, _ => ()
  | _, _, _, .snoc _ _ _ _, _, _, ⟨ρ, .snoc p q⟩, 𝓼 =>
      (envComp ⟨ρ, p⟩ 𝓼, (val q).hom.map 𝓼)

@[inherit_doc envComp] scoped infixr:66 " ⊚ " => GST.envComp

/-- Agda: `_⊚₁_` (GST/TypeSemantics.agda). -/
theorem envComp₁ : {S S' S'' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {Γ'' : Cx S''} →
    {p p' : RnHom Γ' Γ} → {𝓼 𝓼' : Psh.El (𝓔 Γ') Γ''} → ((Γ' →ᵣ Γ) ∋ p ~ p') →
    ((𝓔 Γ').obj Γ'' ∋ 𝓼 ~ 𝓼') → (𝓔 Γ).obj Γ'' ∋ p ⊚ 𝓼 ~ p' ⊚ 𝓼'
  | _, _, _, .nil, _, _, _, _, _, _, _, _ => trivial
  | _, _, _, .snoc _ x _ _, _, _, ⟨_, .snoc _ q⟩, ⟨_, .snoc _ q'⟩, _, _, e, 𝓮 =>
      ⟨envComp₁ (fun y r => e y (.unionL r)) 𝓮, val₁ q q' (e x (.unionR .single)) 𝓮⟩

/-- Agda: `ntl⊚` (GST/TypeSemantics.agda). -/
theorem envComp_ntl : {S S' S'' S''' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} →
    {Γ'' : Cx S''} → {Γ''' : Cx S'''} → (p : RnHom Γ' Γ) → (p' : RnHom Γ''' Γ'') →
    (𝓼 : Psh.El (𝓔 Γ') Γ'') →
    (𝓔 Γ).obj Γ''' ∋ p ⊚ (((𝓔 Γ').act p').map 𝓼) ~ ((𝓔 Γ).act p').map (p ⊚ 𝓼)
  | _, _, _, _, .nil, _, _, _, _, _, _ => trivial
  | _, _, _, _, .snoc _ _ _ _, _, _, _, ⟨ρ, .snoc p q⟩, p', 𝓼 =>
      ⟨envComp_ntl ⟨ρ, p⟩ p' 𝓼, (val q).ntl p' 𝓼⟩

/-- Agda: `renVal` (GST/TypeSemantics.agda). -/
theorem renVal : {S S' S'' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {Γ'' : Cx S''} →
    {A : Ty} → {x : Atom} → (p : RnHom Γ' Γ) → (𝓼 : Psh.El (𝓔 Γ') Γ'') →
    (q : (x, A) isIn Γ) → (q' : (p.rn x, A) isIn Γ') →
    (𝓓 A).obj Γ'' ∋ (val q').hom.map 𝓼 ~ (val q).hom.map (p ⊚ 𝓼)
  | _, _, _, _, _, _, _, _, ⟨_, .snoc _ p'⟩, 𝓼, .new, q => by
      cases IsIn.unique p' q
      exact ((𝓓 _).obj _).rfl' ((val p').hom.map 𝓼)
  | _, _, _, _, _, _, _, _, ⟨ρ, .snoc p _⟩, 𝓼, .old q, q' => renVal ⟨ρ, p⟩ 𝓼 q q'

/-- Agda: `renWk` (GST/TypeSemantics.agda). -/
theorem renWk : {S S' S'' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {Γ'' : Cx S''} →
    {x : Atom} → {h : x ∉ᶠ S'} → (p : RnHom Γ' Γ) → (A : Ty) →
    (𝓼 : Psh.El (𝓔 Γ') Γ'') → (𝓪 : Psh.El (𝓓 A) Γ'') →
    wkRnHom p A h ⊚ (𝓼, 𝓪) = p ⊚ 𝓼
  | _, _, _, .nil, _, _, _, _, _, _, _, _ => rfl
  | _, _, _, .snoc _ _ _ _, _, _, _, _, ⟨ρ, .snoc p q⟩, A, 𝓼, 𝓪 =>
      congrArg (fun z => (z, (val q).hom.map 𝓼)) (renWk ⟨ρ, p⟩ A 𝓼 𝓪)

/-- Agda: `⊚unit` (GST/TypeSemantics.agda). -/
theorem envComp_unit : {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} →
    (𝓼 : Psh.El (𝓔 Γ) Γ') → RnHom.id Γ ⊚ 𝓼 = 𝓼
  | _, _, .nil, _, _ => rfl
  | _, _, .snoc Γ _ A _, _, 𝓼 =>
      congrArg (fun z => (z, 𝓼.2))
        ((renWk (RnHom.id Γ) A 𝓼.1 𝓼.2).trans (envComp_unit 𝓼.1))

/-- Lean-only: the semantic value of the transported `isIn` evidence produced by
`liftRn` is the second component of the environment. -/
theorem val_new_cast {S S'' : Fset} {Γ : Cx S} {Γ'' : Cx S''} {A : Ty} {x z : Atom}
    {h : x ∉ᶠ S} (e : x = z) (𝓼 : Psh.El (𝓔 Γ) Γ'') (𝓪 : Psh.El (𝓓 A) Γ'') :
    (val (castIsIn e (IsIn.new (Γ := Γ) (A := A) (h := h)))).hom.map (𝓼, 𝓪) = 𝓪 := by
  cases e; rfl

/-- Agda: `renUpdate` (GST/TypeSemantics.agda). -/
theorem renUpdate {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''} {A : Ty}
    {x x' : Atom} (hx : x ∉ᶠ S) (hx' : x' ∉ᶠ S') (p : RnHom Γ' Γ)
    (𝓼 : Psh.El (𝓔 Γ') Γ'') (𝓪 : Psh.El (𝓓 A) Γ'') :
    (𝓔 (Γ ⨟ x ∶ A ∣ hx)).obj Γ'' ∋
      liftRnHom p x x' A hx hx' ⊚ (𝓼, 𝓪) ~ (p ⊚ 𝓼, 𝓪) := by
  refine ⟨?_, ?_⟩
  · refine ((𝓔 Γ).obj Γ'').trans'
      (envComp₁ (p := ⟨p.rn ∘/ x ≔ʳ x', rnTypingExt (rnUpdate_fresh p.rn hx)
          (wkRn hx' p.pf)⟩)
        (p' := wkRnHom p A hx')
        ((rnSetd (dom Γ)).symm' (rnUpdate_fresh p.rn hx))
        (((𝓔 (Γ' ⨟ x' ∶ A ∣ hx')).obj Γ'').rfl' (𝓼, 𝓪))) ?_
    exact ((𝓔 Γ).obj Γ'').relOfEq (renWk p A 𝓼 𝓪)
  · exact ((𝓓 A).obj Γ'').relOfEq
      (val_new_cast (Rn.update_eq p.rn x x').symm 𝓼 𝓪)

end GST

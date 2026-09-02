import GST.TypeSemantics

/-!
# Reification and reflection

Port of `agda-code/agda/GST/ReifyReflect.agda`.

`reify A` (Agda `↓ A`) and `reflect A` (Agda `↑ A`) are defined by mutual structural
recursion on the type `A`.  Agda's parameterised module `reify` (which names the
fresh atom `x`, the reflected variable `𝔁`, the applied value `𝓫` and its reification
`↓𝓫`) has no Lean counterpart — a `where` block would leave the mutual recursion — so
those abbreviations are inlined, and the naturality proof reintroduces them as local
`let`s.

The fresh atom is Agda's `new (supp Γ)`, here `Fset.new (dom Γ)`.
-/

namespace GST

open WSLN

/-! ## Reification and reflection -/

mutual

/-- Agda: `↓` (GST/ReifyReflect.agda). -/
def reify : (A : Ty) → Psh.Hom (𝓓 A) (Norm A)
  | 𝐍𝐚𝐭 => Psh.Hom.id (Norm 𝐍𝐚𝐭)
  | A ⇒ B =>
    { hom := fun {S} {_} =>
        { map := fun φ =>
            ⟨𝛌 A (Fset.new S ． ((reify B).hom.map (φ.hom.map
                (RnHom.proj A (Fset.new_notMem S),
                  (reflect A).hom.map (newvar (Fset.new S) A (Fset.new_notMem S))))).nt),
             Nf.lam (h := Fset.new_notMem S)
               (castNf (concAbs' (Fset.new S) _).symm
                 ((reify B).hom.map (φ.hom.map
                   (RnHom.proj A (Fset.new_notMem S),
                     (reflect A).hom.map
                       (newvar (Fset.new S) A (Fset.new_notMem S))))).pf)
               (fresh_abs (Fset.new S) _)⟩
          resp := fun {_ _} e =>
            congrArg (fun c => 𝛌 A (Fset.new S ． c))
              ((reify B).hom.resp (e (RnHom.proj A (Fset.new_notMem S),
                (reflect A).hom.map
                  (newvar (Fset.new S) A (Fset.new_notMem S))))) }
      ntl := fun {S S'} {Γ} {Γ'} p φ => by
        let x : Atom := Fset.new S
        let x' : Atom := Fset.new S'
        have hx : x ∉ᶠ S := Fset.new_notMem S
        have hx' : x' ∉ᶠ S' := Fset.new_notMem S'
        let p' : RnHom (Γ' ⨟ x' ∶ A ∣ hx') (Γ ⨟ x ∶ A ∣ hx) :=
          liftRnHom p x x' A hx hx'
        let 𝔁 : Psh.El (𝓓 A) (Γ ⨟ x ∶ A ∣ hx) :=
          (reflect A).hom.map (newvar x A hx)
        let 𝔁' : Psh.El (𝓓 A) (Γ' ⨟ x' ∶ A ∣ hx') :=
          (reflect A).hom.map (newvar x' A hx')
        let t : Tm0 := ((reify B).hom.map (φ.hom.map (RnHom.proj A hx, 𝔁))).nt
        have p'𝔁 : (𝓓 A).obj (Γ' ⨟ x' ∶ A ∣ hx') ∋ 𝔁' ~ ((𝓓 A).act p').map 𝔁 :=
          ((𝓓 A).obj _).trans'
            (((𝓓 A).obj _).symm'
              ((reflect A).hom.resp
                (show (Neut A).obj (Γ' ⨟ x' ∶ A ∣ hx') ∋
                    ((Neut A).act p').map (newvar x A hx) ~ newvar x' A hx' from
                  congrArg (fun z => (𝐯z : Tm0)) (Rn.update_eq p.rn x x'))))
            ((reflect A).ntl p' (newvar x A hx))
        have 𝓮 : (𝓓 B).obj (Γ' ⨟ x' ∶ A ∣ hx') ∋
            φ.hom.map (p ∘ᵣ RnHom.proj A hx', 𝔁') ~
              ((𝓓 B).act p').map (φ.hom.map (RnHom.proj A hx, 𝔁)) :=
          ((𝓓 B).obj _).trans'
            (φ.hom.resp
              (show (yon Γ ×^ 𝓓 A).obj (Γ' ⨟ x' ∶ A ∣ hx') ∋
                  (p ∘ᵣ RnHom.proj A hx', 𝔁') ~
                    (RnHom.proj A hx ∘ᵣ p', ((𝓓 A).act p').map 𝔁) from
                ⟨rnUpdate_fresh p.rn hx, p'𝔁⟩))
            (φ.ntl p' (RnHom.proj A hx, 𝔁))
        have k' : ((reify B).hom.map (φ.hom.map (p ∘ᵣ RnHom.proj A hx', 𝔁'))).nt
            = ((p.rn ∘/ x ≔ʳ x') : Rn) * t :=
          ((reify B).hom.resp 𝓮).trans
            ((reify B).ntl p' (φ.hom.map (RnHom.proj A hx, 𝔁)))
        show 𝛌 A (x' ． ((reify B).hom.map
              (φ.hom.map (p ∘ᵣ RnHom.proj A hx', 𝔁'))).nt) = p.rn * 𝛌 A (x ． t)
        rw [k']
        show 𝛌 A (x' ． ((p.rn ∘/ x ≔ʳ x') : Rn) * t) = 𝛌 A (p.rn * (x ． t))
        rw [rnAbs p.rn x x' t]
        intro y hy hne e
        refine Fset.not_mem_of_notMem hx' ?_
        rw [e]
        exact rnDom p.pf (Fset.mem_left_of_notMem_right
          (supp_deriv (nfDeriv ((reify B).hom.map
            (φ.hom.map (RnHom.proj A hx, 𝔁))).pf) hy)
          (.single fun ee => hne ee.symm)) }

/-- Agda: `↑` (GST/ReifyReflect.agda). -/
def reflect : (A : Ty) → Psh.Hom (Neut A) (𝓓 A)
  | 𝐍𝐚𝐭 => neuHom
  | A ⇒ B =>
    { hom := fun {_} {_} =>
        { map := fun a =>
            { hom := fun {_} {_} =>
                { map := fun z =>
                    (reflect B).hom.map
                      ⟨(z.1.rn * a.ut) ∙ ((reify A).hom.map z.2).nt,
                       .app (rnNe z.1.pf a.pf) ((reify A).hom.map z.2).pf⟩
                  resp := fun {u v} e =>
                    (reflect B).hom.resp (by
                      show (u.1.rn * a.ut) ∙ ((reify A).hom.map u.2).nt
                          = (v.1.rn * a.ut) ∙ ((reify A).hom.map v.2).nt
                      rw [rnRespSupp u.1.rn v.1.rn a.ut fun y r =>
                            e.1 y (supp_deriv (neDeriv a.pf) r),
                          (reify A).hom.resp e.2]) }
              ntl := fun {_ _} {_} {_} p' z =>
                ((𝓓 B).obj _).trans'
                  ((reflect B).hom.resp (by
                    show (Rn.comp p'.rn z.1.rn * a.ut)
                          ∙ ((reify A).hom.map (((𝓓 A).act p').map z.2)).nt
                        = (p'.rn * (z.1.rn * a.ut))
                          ∙ (p'.rn * ((reify A).hom.map z.2).nt)
                    have h₁ : ((reify A).hom.map (((𝓓 A).act p').map z.2)).nt
                        = p'.rn * ((reify A).hom.map z.2).nt := (reify A).ntl p' z.2
                    rw [rnAssoc z.1.rn p'.rn a.ut, h₁]))
                  ((reflect B).ntl p'
                    ⟨(z.1.rn * a.ut) ∙ ((reify A).hom.map z.2).nt,
                     .app (rnNe z.1.pf a.pf) ((reify A).hom.map z.2).pf⟩) }
          resp := fun {_ _} e => fun {_ _} z =>
            (reflect B).hom.resp
              (congrArg (fun t => (z.1.rn * t) ∙ ((reify A).hom.map z.2).nt) e) }
      ntl := fun {_ _} {_} {_} p a => fun {_ _} z =>
        (reflect B).hom.resp
          (congrArg (fun t => t ∙ ((reify A).hom.map z.2).nt)
            (rnAssoc p.rn z.1.rn a.ut).symm) }

end

/-! ## Abbreviations -/

/-- Agda: `↓₀` (GST/ReifyReflect.agda). -/
def reifyTm (A : Ty) {S : Fset} {Γ : Cx S} (𝓪 : Psh.El (𝓓 A) Γ) : Tm0 :=
  ((reify A).hom.map 𝓪).nt

/-- Agda: `↓₀⊢` (GST/ReifyReflect.agda). -/
def reifyNf {A : Ty} {S : Fset} {Γ : Cx S} (𝓪 : Psh.El (𝓓 A) Γ) :
    Γ ⊢ⁿ reifyTm A 𝓪 ∶ A := ((reify A).hom.map 𝓪).pf

/-- Agda: `↑₀` (GST/ReifyReflect.agda). -/
def reflectEl {A : Ty} {a : Tm0} {S : Fset} {Γ : Cx S} (q : Γ ⊢ᵘ a ∶ A) :
    Psh.El (𝓓 A) Γ := (reflect A).hom.map ⟨a, q⟩

/-! ## Initial environment -/

/-- Agda: `𝓼₀` (GST/ReifyReflect.agda). -/
def env₀ : {S : Fset} → (Γ : Cx S) → Psh.El (𝓔 Γ) Γ
  | _, .nil => ()
  | _, .snoc Γ _ A h =>
      (((𝓔 Γ).act (RnHom.proj A h)).map (env₀ Γ), reflectEl (.var .new))

end GST

import GST.Renaming

/-!
# The category of renamings and presheaves on it

Port of `agda-code/agda/GST/Presheaf.agda`.

The objects of the category `ℝ` are contexts and the morphisms are well-typed
renamings; `Psh` is the type of presheaves on `ℝ`, `Psh.Hom` the type of natural
transformations.  The file ends with the cartesian closed structure: terminal
presheaf, products, the representable presheaf (Agda's `よ`, Yoneda) and the
exponential together with evaluation and currying.

Agda's `Set`/`Set₁` become `Type`/`Type 1`; nothing here needs universe
polymorphism, so `Psh : Type 1` and `Psh.Hom A B : Type`.

`Presheaf.agda` also opens `GST.Syntax`, `GST.TypeSystem`, `GST.WellScoped`,
`GST.Substitution`, `GST.Admissible`, `GST.UniqueTypes` and `GST.NormalForm`, but uses
nothing from them: the whole file only needs typed renamings and setoids, so this
module imports `GST.Renaming` alone (which re-exports `GST.Setoid` and `GST.Context`).

Agda's `Identity^ℝ` and `Composition^ℝ` instances only overload Agda's `id` and `_∘_`
for natural transformations; the port names them `Psh.Hom.id` and `Psh.Hom.comp`
directly, so there is nothing to overload.
-/

namespace GST

open WSLN

/-! ## The category `ℝ` of renamings -/

structure RnHom {S' S : Fset} (Γ' : Cx S') (Γ : Cx S) : Type where
  /-- The underlying renaming. -/
  rn : Rn
  /-- The proof that it is well typed. -/
  pf : Γ' ⊢ʳ rn ∶ Γ

/-- The setoid of morphisms: two renamings are identified when they agree on the domain of the
source context. -/
def rnHomSetd {S' S : Fset} (Γ' : Cx S') (Γ : Cx S) : Setd where
  El := RnHom Γ' Γ
  rel p p' := rnSetd (dom Γ) ∋ p.rn ~ p'.rn
  rfl' p := (rnSetd (dom Γ)).rfl' p.rn
  symm' e := (rnSetd (dom Γ)).symm' e
  trans' e e' := (rnSetd (dom Γ)).trans' e e'

@[inherit_doc rnHomSetd] scoped infix:60 " →ᵣ " => GST.rnHomSetd

def RnHom.id {S : Fset} (Γ : Cx S) : RnHom Γ Γ where
  rn := Rn.id
  pf := rnTypingId Γ

/-- Note that the underlying renamings compose in the opposite order. -/
def RnHom.comp {S S' S'' : Fset} {Γ : Cx S} {Γ' : Cx S'} {Γ'' : Cx S''}
    (p : RnHom Γ' Γ) (q : RnHom Γ'' Γ') : RnHom Γ'' Γ where
  rn := Rn.comp q.rn p.rn
  pf := rnTypingComp q.pf p.pf

@[inherit_doc RnHom.comp] scoped infixr:65 " ∘ᵣ " => GST.RnHom.comp

def RnHom.proj {S : Fset} {Γ : Cx S} {x : Atom} (A : Ty) (h : x ∉ᶠ S) :
    RnHom (Γ ⨟ x ∶ A ∣ h) Γ where
  rn := Rn.id
  pf := wkRn h (rnTypingId Γ)

def wkRnHom {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} {x : Atom} (p : RnHom Γ' Γ) (A : Ty)
    (h : x ∉ᶠ S') : RnHom (Γ' ⨟ x ∶ A ∣ h) Γ where
  rn := p.rn
  pf := wkRn h p.pf

def liftRnHom {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} (p : RnHom Γ' Γ) (x x' : Atom)
    (A : Ty) (hx : x ∉ᶠ S) (hx' : x' ∉ᶠ S') :
    RnHom (Γ' ⨟ x' ∶ A ∣ hx') (Γ ⨟ x ∶ A ∣ hx) where
  rn := p.rn ∘/ x ≔ʳ x'
  pf := liftRn hx hx' p.pf

/-! ## Presheaves on `ℝ` -/

structure Psh : Type 1 where
  /-- The setoid of elements at a context. -/
  obj : {S : Fset} → Cx S → Setd
  /-- The contravariant action on morphisms. -/
  cong : {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} →
    Setd[ (Γ' →ᵣ Γ) ⟶ (obj Γ ⇨ obj Γ') ]
  unit : {S : Fset} → (Γ : Cx S) →
    (obj Γ ⇨ obj Γ) ∋ cong.map (RnHom.id Γ) ~ Setd.Hom.id (obj Γ)
  assoc : {S S' S'' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → {Γ'' : Cx S''} →
    (p : RnHom Γ' Γ) → (q : RnHom Γ'' Γ') →
    (obj Γ ⇨ obj Γ'') ∋ cong.map (p ∘ᵣ q) ~ (cong.map q).comp (cong.map p)

/-- Lean-only abbreviation: the elements a presheaf assigns to a context.  Agda writes
`∣ A ⊙ Γ ∣`. -/
abbrev Psh.El (A : Psh) {S : Fset} (Γ : Cx S) : Type := (A.obj Γ).El

def Psh.act (A : Psh) {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} (p : RnHom Γ' Γ) :
    Setd[ A.obj Γ ⟶ A.obj Γ' ] := A.cong.map p

/-! ## Natural transformations -/

structure Psh.Hom (A B : Psh) : Type where
  /-- The family of maps. -/
  hom : {S : Fset} → {Γ : Cx S} → Setd[ A.obj Γ ⟶ B.obj Γ ]
  /-- Naturality. -/
  ntl : {S S' : Fset} → {Γ : Cx S} → {Γ' : Cx S'} → (p : RnHom Γ' Γ) →
    (A.obj Γ ⇨ B.obj Γ') ∋ hom.comp (A.act p) ~ (B.act p).comp hom

def Psh.Hom.id (A : Psh) : Psh.Hom A A where
  hom := Setd.Hom.id (A.obj _)
  ntl _ x := (A.obj _).rfl' ((A.act _).map x)

def Psh.Hom.comp {A B C : Psh} (g : Psh.Hom B C) (f : Psh.Hom A B) : Psh.Hom A C where
  hom := g.hom.comp f.hom
  ntl p x := (C.obj _).trans' (g.hom.resp (f.ntl p x)) (g.ntl p (f.hom.map x))

/-- The setoid of natural transformations.

As in Agda, the context of the compared elements is implicit in `rel`, so the proofs
below bind it with `fun {_ _} x => …`. -/
def pshHomSetd (A B : Psh) : Setd where
  El := Psh.Hom A B
  rel φ ψ := ∀ {S : Fset} {Γ : Cx S} (x : (A.obj Γ).El),
    B.obj Γ ∋ φ.hom.map x ~ ψ.hom.map x
  rfl' φ := fun {_ _} x => (B.obj _).rfl' (φ.hom.map x)
  symm' e := fun {_ _} x => (B.obj _).symm' (e x)
  trans' e e' := fun {_ _} x => (B.obj _).trans' (e x) (e' x)

@[inherit_doc pshHomSetd] scoped infix:55 " ⟶^ " => GST.pshHomSetd

/-! ## Terminal presheaf -/

def Psh.one : Psh where
  obj _ := Setd.one
  cong := { map := fun _ => Setd.Hom.id Setd.one, resp := fun _ _ => trivial }
  unit _ _ := trivial
  assoc _ _ _ := trivial

def Psh.bang {A : Psh} : Psh.Hom A Psh.one where
  hom := { map := fun _ => (), resp := fun _ => trivial }
  ntl _ _ := trivial

/-! ## Presheaf product -/

/-- Product of presheaves. -/
def Psh.prod (A B : Psh) : Psh where
  obj Γ := A.obj Γ ⊗ B.obj Γ
  cong := fun {_ _} {_} {_} =>
    { map := fun p =>
        { map := fun x => ((A.act p).map x.1, (B.act p).map x.2)
          resp := fun e => ⟨(A.act p).resp e.1, (B.act p).resp e.2⟩ }
      resp := fun e x => ⟨A.cong.resp e x.1, B.cong.resp e x.2⟩ }
  unit Γ x := ⟨A.unit Γ x.1, B.unit Γ x.2⟩
  assoc p q x := ⟨A.assoc p q x.1, B.assoc p q x.2⟩

@[inherit_doc Psh.prod] scoped infixl:70 " ×^ " => GST.Psh.prod

def Psh.fst {A B : Psh} : Psh.Hom (A ×^ B) A where
  hom := Setd.fst
  ntl p x := (A.obj _).rfl' ((A.act p).map x.1)

def Psh.snd {A B : Psh} : Psh.Hom (A ×^ B) B where
  hom := Setd.snd
  ntl p x := (B.obj _).rfl' ((B.act p).map x.2)

def Psh.pair {A B C : Psh} (φ : Psh.Hom C A) (ψ : Psh.Hom C B) : Psh.Hom C (A ×^ B) where
  hom := Setd.pair φ.hom ψ.hom
  ntl p x := ⟨φ.ntl p x, ψ.ntl p x⟩

def Psh.prodMap {A A' B B' : Psh} (φ : Psh.Hom A A') (ψ : Psh.Hom B B') :
    Psh.Hom (A ×^ B) (A' ×^ B') :=
  Psh.pair (φ.comp Psh.fst) (ψ.comp Psh.snd)

/-! ## Representable presheaf -/

/-- The Yoneda embedding. -/
def yon {S : Fset} (Γ : Cx S) : Psh where
  obj Γ' := Γ' →ᵣ Γ
  cong := fun {_ _} {_} {_} =>
    { map := fun p =>
        { map := fun q => q ∘ᵣ p
          resp := fun e x r => congrArg p.rn (e x r) }
      resp := fun e q x r => e (q.rn x) (rnDom q.pf r) }
  unit _ _ _ _ := rfl
  assoc _ _ _ _ _ := rfl

def yonMap {S S' : Fset} {Γ : Cx S} {Γ' : Cx S'} (p : RnHom Γ' Γ) :
    Psh.Hom (yon Γ') (yon Γ) where
  hom := { map := fun q => p ∘ᵣ q, resp := fun e x r => e (p.rn x) (rnDom p.pf r) }
  ntl _ _ _ _ := rfl

/-! ## Presheaf exponential -/

/-- Exactly as in Agda, the elements of the exponential at `Γ` are the natural transformations
`yon Γ ×^ A ⟶^ B`. -/
def Psh.exp (A B : Psh) : Psh where
  obj Γ := yon Γ ×^ A ⟶^ B
  cong := fun {_ _} {_} {_} =>
    { map := fun p =>
        { map := fun φ => φ.comp (Psh.prodMap (yonMap p) (Psh.Hom.id A))
          resp := fun e => fun {_ _} x =>
            e ((Psh.prodMap (yonMap p) (Psh.Hom.id A)).hom.map x) }
      resp := fun e φ => fun {_ _} x =>
        φ.hom.resp ⟨fun y r => congrArg x.1.rn (e y r), (A.obj _).rfl' x.2⟩ }
  unit _ φ := fun {_ _} x => φ.hom.resp ⟨fun _ _ => rfl, (A.obj _).rfl' x.2⟩
  assoc _ _ φ := fun {_ _} x => φ.hom.resp ⟨fun _ _ => rfl, (A.obj _).rfl' x.2⟩

@[inherit_doc Psh.exp] scoped infixr:60 " →^ " => GST.Psh.exp

def Psh.ev {A B : Psh} : Psh.Hom ((A →^ B) ×^ A) B where
  hom := fun {_} {Γ} =>
    { map := fun x => x.1.hom.map (RnHom.id Γ, x.2)
      resp := fun {u v} e =>
        (B.obj Γ).trans' (e.1 (RnHom.id Γ, u.2))
          (v.1.hom.resp ⟨fun _ _ => rfl, e.2⟩) }
  ntl := fun {_ _} {Γ} {Γ'} p x =>
    calc B.obj Γ' ∋ x.1.hom.map (p ∘ᵣ RnHom.id Γ', (A.act p).map x.2)
          ~ x.1.hom.map (RnHom.id Γ ∘ᵣ p, (A.act p).map x.2) :=
        x.1.hom.resp ⟨fun _ _ => rfl, (A.obj Γ').rfl' ((A.act p).map x.2)⟩
      B.obj Γ' ∋ _ ~ (B.act p).map (x.1.hom.map (RnHom.id Γ, x.2)) :=
        x.1.ntl p (RnHom.id Γ, x.2)

def Psh.cur {A B C : Psh} (φ : Psh.Hom (C ×^ A) B) : Psh.Hom C (A →^ B) where
  hom := fun {_} {_} =>
    { map := fun c =>
        { hom := fun {_} {_} =>
            { map := fun x => φ.hom.map ((C.act x.1).map c, x.2)
              resp := fun e => φ.hom.resp ⟨C.cong.resp e.1 c, e.2⟩ }
          ntl := fun {_ _} {_} {Γ₂} p x =>
            calc B.obj Γ₂ ∋ φ.hom.map ((C.act (x.1 ∘ᵣ p)).map c, (A.act p).map x.2)
                  ~ φ.hom.map ((C.act p).map ((C.act x.1).map c), (A.act p).map x.2) :=
                φ.hom.resp ⟨C.assoc x.1 p c, (A.obj Γ₂).rfl' ((A.act p).map x.2)⟩
              B.obj Γ₂ ∋ _ ~ (B.act p).map (φ.hom.map ((C.act x.1).map c, x.2)) :=
                φ.ntl p ((C.act x.1).map c, x.2) }
      resp := fun e => fun {_ _} x =>
        φ.hom.resp ⟨(C.act x.1).resp e, (A.obj _).rfl' x.2⟩ }
  ntl p c := fun {_ _} x =>
    φ.hom.resp ⟨(C.obj _).symm' (C.assoc p x.1 c), (A.obj _).rfl' x.2⟩

end GST

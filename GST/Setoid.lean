import WSLN

/-!
# Setoids

Port of `agda-code/agda/GST/Setoid.agda`.

A `Setd` is a type together with an equivalence relation.  Agda's `Set`/`Set₁` become
`Type`/`Type 1`: nothing in the development needs universe polymorphism.  Every
setoid used here (renamings, substitutions, normal forms, products, exponentials,
natural transformations) has a `Prop`-valued relation, so `rel` lands in `Prop` and
the Agda proofs of `isProp`-style side conditions disappear.

Core's `Setoid` class is deliberately *not* reused: it is an unbundled class over a
fixed carrier, whereas here setoids are the objects of a category and must be bundled.

Agda's chain-reasoning combinators — the wrapper `~Rel` with its constructor `~rel`,
`~begin_∋_`, `step~` (`_~⟨_⟩_`), `step~°` (`_~°⟨_⟩_`), `_~⟨⟩_` and `_~∎` — are
replaced by Lean's `calc`, enabled by the `Trans` instance below; the `test` module
of the Agda source becomes the `example` at the end of this file.
-/

namespace GST

open WSLN

/-! ## Setoids -/

/-- Agda: `Setd` (GST/Setoid.agda). -/
structure Setd : Type 1 where
  /-- Agda: `∣_∣`. The carrier. -/
  El : Type
  /-- Agda: `_∋_~_`. The equivalence relation. -/
  rel : El → El → Prop
  /-- Agda: `~Refl`. -/
  rfl' (x : El) : rel x x
  /-- Agda: `~Symm`. -/
  symm' {x y : El} : rel x y → rel y x
  /-- Agda: `~Trans`. -/
  trans' {x y z : El} : rel x y → rel y z → rel x z

@[inherit_doc Setd.rel]
scoped notation:50 A:51 " ∋ " x:51 " ~ " y:51 => Setd.rel A x y

/-- Agda: `~Refl'` (GST/Setoid.agda). -/
theorem Setd.relOfEq (A : Setd) {x x' : A.El} (e : x = x') : A ∋ x ~ x' := by
  cases e; exact A.rfl' x

/-- Chain reasoning: Agda's `~begin_∋_` / `_~⟨_⟩_` / `_~∎` become `calc`. -/
instance (A : Setd) : Trans A.rel A.rel A.rel := ⟨A.trans'⟩

/-! ## Morphisms of setoids -/

/-- Agda: `Setd[_⟶_]` (GST/Setoid.agda). -/
structure Setd.Hom (A B : Setd) : Type where
  /-- Agda: `_₀_`. The underlying function. -/
  map : A.El → B.El
  /-- Agda: `_₁_`. The function respects the relations. -/
  resp {x x' : A.El} : (A ∋ x ~ x') → (B ∋ map x ~ map x')

@[inherit_doc Setd.Hom] scoped notation:25 "Setd[ " A " ⟶ " B " ]" => Setd.Hom A B

/-- Agda: `SetdIdentity` (GST/Setoid.agda). -/
def Setd.Hom.id (A : Setd) : Setd[ A ⟶ A ] where
  map x := x
  resp e := e

/-- Agda: `SetdComp` (GST/Setoid.agda). -/
def Setd.Hom.comp {A B C : Setd} (g : Setd[ B ⟶ C ]) (f : Setd[ A ⟶ B ]) :
    Setd[ A ⟶ C ] where
  map x := g.map (f.map x)
  resp e := g.resp (f.resp e)

/-! ## Discrete and terminal setoids -/

/-- Agda: `Δ` (GST/Setoid.agda). -/
def Setd.disc (A : Type) : Setd where
  El := A
  rel _ _ := True
  rfl' _ := trivial
  symm' _ := trivial
  trans' _ _ := trivial

/-- Agda: `１` (GST/Setoid.agda). -/
def Setd.one : Setd := Setd.disc Unit

/-! ## Products -/

/-- Agda: `_⊗_` (GST/Setoid.agda). -/
def Setd.prod (A B : Setd) : Setd where
  El := A.El × B.El
  rel p q := (A ∋ p.1 ~ q.1) ∧ (B ∋ p.2 ~ q.2)
  rfl' p := ⟨A.rfl' p.1, B.rfl' p.2⟩
  symm' e := ⟨A.symm' e.1, B.symm' e.2⟩
  trans' e e' := ⟨A.trans' e.1 e'.1, B.trans' e.2 e'.2⟩

@[inherit_doc Setd.prod] scoped infixl:70 " ⊗ " => GST.Setd.prod

/-- Agda: `fst` (GST/Setoid.agda). -/
def Setd.fst {A B : Setd} : Setd[ A ⊗ B ⟶ A ] where
  map p := p.1
  resp e := e.1

/-- Agda: `snd` (GST/Setoid.agda). -/
def Setd.snd {A B : Setd} : Setd[ A ⊗ B ⟶ B ] where
  map p := p.2
  resp e := e.2

/-- Agda: `pair` (GST/Setoid.agda). -/
def Setd.pair {A B C : Setd} (f : Setd[ C ⟶ A ]) (g : Setd[ C ⟶ B ]) :
    Setd[ C ⟶ A ⊗ B ] where
  map c := (f.map c, g.map c)
  resp e := ⟨f.resp e, g.resp e⟩

/-- Agda: `_⊗′_` (GST/Setoid.agda). -/
def Setd.prodMap {A A' B B' : Setd} (f : Setd[ A ⟶ A' ]) (g : Setd[ B ⟶ B' ]) :
    Setd[ A ⊗ B ⟶ A' ⊗ B' ] where
  map p := (f.map p.1, g.map p.2)
  resp e := ⟨f.resp e.1, g.resp e.2⟩

/-! ## Exponentials -/

/-- Agda: `_⇨_` (GST/Setoid.agda). -/
def Setd.exp (A B : Setd) : Setd where
  El := Setd[ A ⟶ B ]
  rel f f' := ∀ x, B ∋ f.map x ~ f'.map x
  rfl' f x := B.rfl' (f.map x)
  symm' e x := B.symm' (e x)
  trans' e e' x := B.trans' (e x) (e' x)

@[inherit_doc Setd.exp] scoped infixr:60 " ⇨ " => GST.Setd.exp

/-- Agda: `ev` (GST/Setoid.agda). -/
def Setd.ev {A B : Setd} : Setd[ (A ⇨ B) ⊗ A ⟶ B ] where
  map p := p.1.map p.2
  resp {p p'} e := B.trans' (e.1 p.2) (p'.1.resp e.2)

/-- Agda: `cur` (GST/Setoid.agda). -/
def Setd.cur {A B C : Setd} (f : Setd[ C ⊗ A ⟶ B ]) : Setd[ C ⟶ (A ⇨ B) ] where
  map c := { map := fun a => f.map (c, a), resp := fun e => f.resp ⟨C.rfl' c, e⟩ }
  resp e a := f.resp ⟨e, A.rfl' a⟩

/-! ## Chain reasoning works -/

example (A : Setd) (x y z w : A.El) (p : A ∋ x ~ y) (q : A ∋ y ~ z) (r : A ∋ w ~ z) :
    A ∋ x ~ w :=
  calc A ∋ x ~ y := p
    A ∋ _ ~ z := q
    A ∋ _ ~ w := A.symm' r

end GST

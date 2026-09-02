/-!
# Prelude

Port of Andrew Pitts' Agda library *Well-Scoped Locally Nameless* (`agda-code/agda`)
to Lean 4.

This file holds the few `Prelude/*.agda` items that have no ergonomic Lean-core
counterpart.  Everything else in the Agda prelude maps directly onto core:
`_≡_`/`refl`/`symm`/`trans`/`cong` → `Eq`/`rfl`/`Eq.symm`/`Eq.trans`/`congrArg`,
equality chains → `calc`, `Ø`/`Øelim` → `False`/`absurd`, `∑`/`∃` → `Sigma`/`Subtype`/
`Exists`, `_∧_` → `And`, `hasDecEq` → `DecidableEq`, `List`/`Fin` → core `List`/`Fin`,
`isProp`/`isSet`/`hedberg` → Lean's proof irrelevance (deleted).  Agda's `Dec` maps
onto core `Decidable` for propositions, but GST's typing and conversion judgements
are `Type`-valued — the normalization-by-evaluation semantics eliminates a derivation
into data — so the `Sort`-polymorphic original is kept below.
-/

namespace WSLN

universe u v w w'

/-! ## Vectors -/

/-- Lean core's `Vector` is `Array`-backed; the structural version is kept because
`Distinct`/`##` recurse over it. -/
inductive Vec (A : Type u) : Nat → Type u where
  | nil : Vec A 0
  | cons {n : Nat} (a : A) (as : Vec A n) : Vec A (n + 1)

/-! ## Decidable inhabitation -/

/-- Core's `Decidable` is the `Prop`-valued special case; this is the `Sort`-polymorphic
form, needed because `GST`'s judgements live in `Type`. -/
inductive Dec (α : Sort u) where
  | no (h : α → False)
  | yes (h : α)

/-- Core `Decidable` is the `Prop`-valued case of `Dec`. -/
def Dec.ofDecidable {p : Prop} (inst : Decidable p) : Dec p :=
  match inst with
  | isTrue h => .yes h
  | isFalse h => .no h

/-- Whether the decision was positive; `#guard`-friendly. -/
def Dec.isYes {α : Sort u} : Dec α → Bool
  | .yes _ => true
  | .no _ => false

def Dec.and {α : Sort u} {β : Sort v} : Dec α → Dec β → Dec (PProd α β)
  | .no h, _ => .no fun p => h p.1
  | .yes _, .no h => .no fun p => h p.2
  | .yes a, .yes b => .yes ⟨a, b⟩

/-- If `α` implies `β`, `β` is decidable and `α` is decidable given `β`, then `α` is
decidable. -/
def condDec {α : Sort u} {β : Sort v} (f : α → β) : Dec β → (β → Dec α) → Dec α
  | .no h, _ => .no fun a => h (f a)
  | .yes b, g => g b

/-- Decidability transports along a bi-implication. -/
def Dec.ofIff {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) : Dec α → Dec β
  | .no h => .no fun b => h (g b)
  | .yes a => .yes (f a)

/-! ## Update of functions -/

def updateFn {α : Type u} {β : Sort v} [DecidableEq α] (f : α → β) (x : α) (v : β) :
    α → β :=
  fun y => if x = y then v else f y

-- Agda writes `f ∘/ x := v`; the surface notation is introduced per carrier in
-- `WSLN/Substitution.lean` (`∘/ ≔` for substitutions, `∘/ ≔ʳ` for renamings, …),
-- because Lean has no `UpdateFun` class to disambiguate the carriers.

variable {α : Type u} {β : Sort v} [DecidableEq α]

@[simp] theorem updateFn_eq (f : α → β) (x : α) (v : β) : updateFn f x v x = v := by
  simp [updateFn]

theorem updateFn_neq (f : α → β) (v : β) {x x' : α} (h : ¬ (x = x')) :
    updateFn f x v x' = f x' := by
  simp [updateFn, h]

theorem updateFn_id (f : α → β) (x x' : α) : updateFn f x (f x) x' = f x' := by
  by_cases h : x = x' <;> simp [updateFn, h]

theorem updateFn_comp {β' : Type w} (f : α → β') (g : β' → β) (v : β') (x x' : α) :
    updateFn (fun y => g (f y)) x (g v) x' = g (updateFn f x v x') := by
  by_cases h : x = x' <;> simp [updateFn, h]

/-! ## Dependent transport helpers -/

abbrev subst {A : Sort u} (B : A → Sort v) {x x' : A} (e : x = x') (b : B x) : B x' :=
  e ▸ b

def subst₂ {A : Sort u} {B : Sort v} (C : A → B → Sort w) {x x' : A} {y y' : B}
    (e : x = x') (e' : y = y') (c : C x y) : C x' y' :=
  match e, e' with
  | rfl, rfl => c

def subst₃ {A : Sort u} {B : Sort v} {C : Sort w} (D : A → B → C → Sort w')
    {x x' : A} {y y' : B} {z z' : C}
    (e : x = x') (e' : y = y') (e'' : z = z') (d : D x y z) : D x' y' z' :=
  match e, e', e'' with
  | rfl, rfl, rfl => d

theorem substInj {A : Sort u} (B : A → Sort v) {x x' : A} (e : x = x') {y y' : B x}
    (h : subst B e y = subst B e y') : y = y' := by
  cases e; exact h

theorem substInv {A : Sort u} (B : A → Sort v) {x x' : A} (e : x = x') {y : B x}
    {y' : B x'} (h : y' = subst B e y) : subst B e.symm y' = y := by
  cases e; exact h

end WSLN

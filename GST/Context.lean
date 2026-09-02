import GST.Syntax

/-!
# Typing contexts

Port of `agda-code/agda/GST/Context.agda`.

## Contexts are indexed by their domain

The Agda source declares `Cx` and `dom : Cx → Fset𝔸` by induction-recursion, so that
the constructor `_⨟_∶_` can require `x ∉ dom Γ`.  Lean has no induction-recursion, so
the port makes the domain an *index*:

```lean
inductive Cx : Fset → Type where
  | nil : Cx ∅
  | snoc {S : Fset} (Γ : Cx S) (x : Atom) (A : Ty) (h : x ∉ᶠ S) : Cx (S ∪ ｛ x ｝)
```

`dom Γ` is then the index, and every statement about `dom Γ` is a statement about the
index, so the shapes of the Agda statements are preserved.  Agda's instance-implicit
freshness premise becomes the explicit argument `h`, written `Γ ⨟ x ∶ A ∣ h`.

`isProp∉dom` and `isProp≡` are subsumed by Lean's proof irrelevance.  Agda's `cx⁻¹`
and `decEqCx` compare contexts of one and the same domain: at different domains the
two sides do not even have the same type, and no use in the development needs that
generality.

## `isIn` is data

`_isIn_` is `Type`-valued, exactly as in Agda: `GST/TypeSemantics.lean` computes the
semantic value of a variable by recursion over the membership evidence.  Agda's
`isPropIsIn` is therefore a real theorem here too (`IsIn.unique`); its auxiliary
`isPropIsInHelper`, which only exists to transport along the equality of the two
pairs, is unnecessary because `IsIn.unique` matches on both witnesses directly.
-/

namespace GST

open WSLN

/-! ## Contexts -/

/-- Contexts, with `dom` as an index; see the module docstring. -/
inductive Cx : Fset → Type where
  /-- The empty context. -/
  | nil : Cx ∅
  /-- Context extension; the freshness proof is an explicit argument. -/
  | snoc {S : Fset} (Γ : Cx S) (x : Atom) (A : Ty) (h : x ∉ᶠ S) : Cx (S ∪ ｛ x ｝)

@[inherit_doc Cx.nil] scoped notation "◇" => GST.Cx.nil
@[inherit_doc Cx.snoc]
scoped notation:50 Γ:50 " ⨟ " x:51 " ∶ " A:51 " ∣ " h:51 => GST.Cx.snoc Γ x A h

/-- The domain of a context is its index. -/
abbrev dom {S : Fset} (_ : Cx S) : Fset := S

/-- Freshness for contexts. -/
instance instFiniteSupportCx {S : Fset} : FiniteSupport (Cx S) := ⟨fun _ => S⟩

@[simp] theorem supp_cx {S : Fset} (Γ : Cx S) : supp Γ = dom Γ := rfl

/-- Injectivity of context extension, at a fixed domain. -/
theorem snoc_inj {S : Fset} {Γ Γ' : Cx S} {x : Atom} {A A' : Ty} {h h' : x ∉ᶠ S}
    (e : (Γ ⨟ x ∶ A ∣ h) = (Γ' ⨟ x ∶ A' ∣ h')) : Γ = Γ' ∧ A = A' := by
  cases e; exact ⟨rfl, rfl⟩

instance memDec (x : Atom) {S : Fset} (Γ : Cx S) : Decidable (x ∈ dom Γ) :=
  Fset.decidableMem x S

/-- Decidable equality of contexts, at a fixed domain. -/
instance decEqCx {S : Fset} : DecidableEq (Cx S)
  | .nil, .nil => isTrue rfl
  | .snoc Γ x A _, .snoc Γ' _ A' _ =>
      match decEqCx Γ Γ' with
      | isFalse h => isFalse fun e => h (snoc_inj e).1
      | isTrue hΓ =>
          if hA : A = A' then isTrue (by subst hΓ; subst hA; rfl)
          else isFalse fun e => hA (snoc_inj e).2

/-! ## Context components -/

/-- Context membership: the pair `(x, A)` occurs in `Γ`. -/
inductive IsIn : {S : Fset} → Atom × Ty → Cx S → Type where
  | new {S : Fset} {Γ : Cx S} {x : Atom} {A : Ty} {h : x ∉ᶠ S} :
      IsIn (x, A) (Γ ⨟ x ∶ A ∣ h)
  | old {S : Fset} {Γ : Cx S} {xA : Atom × Ty} {x' : Atom} {A' : Ty} {h : x' ∉ᶠ S}
      (p : IsIn xA Γ) : IsIn xA (Γ ⨟ x' ∶ A' ∣ h)

@[inherit_doc IsIn] scoped infix:40 " isIn " => GST.IsIn

/-- Membership implies domain membership, stated on the raw pair so that `induction`
applies. -/
theorem IsIn.dom_mem {S : Fset} {Γ : Cx S} {xA : Atom × Ty} (h : xA isIn Γ) :
    xA.1 ∈ dom Γ := by
  induction h with
  | new => exact .unionR .single
  | old _ ih => exact .unionL ih

theorem isIn_dom {S : Fset} {Γ : Cx S} {x : Atom} {A : Ty} (h : (x, A) isIn Γ) :
    x ∈ dom Γ := h.dom_mem

/-- The recursion is on the context, not on the membership evidence: `x ∈ dom Γ` is a
`Prop` in Lean, while the result is data. -/
def dom_isIn {S : Fset} : (Γ : Cx S) → {x : Atom} → x ∈ dom Γ → Σ A : Ty, (x, A) isIn Γ
  | .nil, _, h => absurd h (Fset.not_mem_of_notMem .empty)
  | .snoc Γ y B _, x, h =>
      if e : x = y then ⟨B, by cases e; exact .new⟩
      else
        let ⟨A, p⟩ := dom_isIn Γ (Fset.mem_left_of_notMem_right h (.single e))
        ⟨A, .old p⟩

def isInDec {S : Fset} : (Γ : Cx S) → (A : Ty) → (x : Atom) → Dec ((x, A) isIn Γ)
  | .nil, _, _ => .no fun p => nomatch p
  | .snoc Γ y B _, A, x =>
      if e : (y, B) = (x, A) then
        .yes (by cases e; exact .new)
      else
        match isInDec Γ A x with
        | .yes p => .yes (.old p)
        | .no h => .no fun p => by
            cases p with
            | new => exact e rfl
            | old p' => exact h p'

/-! ## Membership evidence is unique -/

theorem IsIn.unique {S : Fset} {Γ : Cx S} {xA : Atom × Ty} :
    ∀ (p p' : xA isIn Γ), p = p'
  | .new, .new => rfl
  | .new, .old p' => absurd p'.dom_mem (Fset.not_mem_of_notMem (by assumption))
  | .old p, .new => absurd p.dom_mem (Fset.not_mem_of_notMem (by assumption))
  | .old p, .old p' => congrArg IsIn.old (IsIn.unique p p')

instance {S : Fset} {Γ : Cx S} {xA : Atom × Ty} : Subsingleton (xA isIn Γ) :=
  ⟨IsIn.unique⟩

/-- Transport membership evidence along an equality of names (Agda uses `subst`). -/
def castIsIn {S : Fset} {Γ : Cx S} {A : Ty} {x x' : Atom} (e : x = x')
    (q : (x, A) isIn Γ) : (x', A) isIn Γ := e ▸ q

end GST

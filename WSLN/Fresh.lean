import WSLN.Atom

/-!
# Finite support and freshness

Port of `agda-code/agda/WSLN/Fresh.agda`.

Agda's `isProp#` is dropped (Lean `Prop` is proof irrelevant).  Agda's `fresh`,
which returns a `Σ`-type, becomes a `Subtype`, since callers project the witness.
-/

namespace WSLN

universe u v

/-! ## Finite support structure -/

/-- Agda: `FiniteSupport` (WSLN/Fresh.agda). -/
class FiniteSupport (A : Type u) where
  /-- Agda: `supp`. -/
  supp : A → Fset

export FiniteSupport (supp)

/-- Agda: `_#_` (WSLN/Fresh.agda). The derived freshness relation. -/
def Fresh {A : Type u} [FiniteSupport A] (x : Atom) (a : A) : Prop :=
  Fset.NotMem x (supp a)

@[inherit_doc Fresh]
scoped infix:50 " # " => WSLN.Fresh

/-- Agda: `fresh` (WSLN/Fresh.agda). -/
def fresh {A : Type u} [FiniteSupport A] (a : A) : { x : Atom // x # a } :=
  ⟨Fset.new (supp a), Fset.new_notMem (supp a)⟩

/-- Agda: `#?` (WSLN/Fresh.agda). -/
instance decidableFresh {A : Type u} [FiniteSupport A] (x : Atom) (a : A) :
    Decidable (x # a) :=
  Fset.decidableNotMem x (supp a)

/-! ## Instances -/

/-- Agda: `FiniteSupport𝔸` (WSLN/Fresh.agda). -/
instance instFiniteSupportAtom : FiniteSupport Atom := ⟨fun x => ｛ x ｝⟩

/-- Agda: `FiniteSupportFset𝔸` (WSLN/Fresh.agda). -/
instance instFiniteSupportFset : FiniteSupport Fset := ⟨id⟩

/-- Agda: `FiniteSupportFin` (WSLN/Fresh.agda). -/
instance instFiniteSupportFin {n : Nat} : FiniteSupport (Fin n) := ⟨fun _ => ∅⟩

/-- Agda: `FiniteSupport×` (WSLN/Fresh.agda). -/
instance instFiniteSupportProd {A : Type u} {B : Type v} [FiniteSupport A]
    [FiniteSupport B] : FiniteSupport (A × B) :=
  ⟨fun p => supp p.1 ∪ supp p.2⟩

/-- Agda: `suppList` (WSLN/Fresh.agda). -/
def suppList {A : Type u} [FiniteSupport A] : List A → Fset
  | [] => ∅
  | a :: as => supp a ∪ suppList as

/-- Agda: `FiniteSupportList` (WSLN/Fresh.agda). -/
instance instFiniteSupportList {A : Type u} [FiniteSupport A] : FiniteSupport (List A) :=
  ⟨suppList⟩

/-- Agda: `suppVec` (WSLN/Fresh.agda). -/
def suppVec {A : Type u} [FiniteSupport A] : {n : Nat} → Vec A n → Fset
  | _, .nil => ∅
  | _, .cons a as => supp a ∪ suppVec as

/-- Agda: `FiniteSupportVec` (WSLN/Fresh.agda). -/
instance instFiniteSupportVec {A : Type u} [FiniteSupport A] {n : Nat} :
    FiniteSupport (Vec A n) :=
  ⟨suppVec⟩

/-- Agda: `#symm` (WSLN/Fresh.agda). -/
theorem fresh_symm {x y : Atom} (h : x # y) : y # x :=
  .single (Ne.symm (Fset.ne_of_notMem_single h))

/-! ## Freshness for tuples of mutually distinct atoms -/

/-- Agda: `distinct_∉_` (WSLN/Fresh.agda).

Cf. A. Charguéraud, *The Locally Nameless Representation*, J. Autom. Reasoning
49 (2012) section 7.1. -/
inductive Distinct : {n : Nat} → Vec Atom n → Fset → Prop where
  /-- Agda: `##◇`. -/
  | nil {S : Fset} : Distinct Vec.nil S
  /-- Agda: `##::`. -/
  | cons {n : Nat} {xs : Vec Atom n} {x : Atom} {S : Fset}
      (hx : x ∉ᶠ S) (hxs : Distinct xs (｛ x ｝ ∪ S)) : Distinct (Vec.cons x xs) S

/-- Agda: `distinct⊆` (WSLN/Fresh.agda). -/
theorem distinct_subset {n : Nat} {xs : Vec Atom n} {S S' : Fset}
    (h : Distinct xs S') (hs : S ⊆ S') : Distinct xs S := by
  induction h generalizing S with
  | nil => exact .nil
  | @cons n xs x S' hx hxs ih =>
      exact .cons (Fset.subset_notMem hs hx)
        (ih (Fset.union_subset_union Fset.subset_refl hs))

/-- Agda: `distinct｛｝` (WSLN/Fresh.agda). -/
theorem distinct_single {n : Nat} {xs : Vec Atom n} {x : Atom}
    (h : Distinct xs ｛ x ｝) : x # xs := by
  induction n generalizing x with
  | zero => cases xs; exact .empty
  | succ n ih =>
      cases xs with
      | cons y ys =>
          cases h with
          | cons hy hys =>
              exact .union (.single (Ne.symm (Fset.ne_of_notMem_single hy)))
                (ih (distinct_subset hys Fset.subset_union_right))

/-- Agda: `distinct::₁` (WSLN/Fresh.agda). -/
theorem distinct_cons₁ {n : Nat} {xs : Vec Atom n} {x : Atom} {S : Fset}
    (h : Distinct (Vec.cons x xs) S) : Distinct xs S := by
  cases h with
  | cons _ hxs => exact distinct_subset hxs Fset.subset_union_right

/-- Agda: `distinct::₂` (WSLN/Fresh.agda). -/
theorem distinct_cons₂ {n : Nat} {xs : Vec Atom n} {x : Atom} {S : Fset}
    (h : Distinct (Vec.cons x xs) S) : x ∉ᶠ S := by
  cases h with
  | cons hx _ => exact hx

/-- Agda: `distinct::₃` (WSLN/Fresh.agda). -/
theorem distinct_cons₃ {n : Nat} {xs : Vec Atom n} {x : Atom} {S : Fset}
    (h : Distinct (Vec.cons x xs) S) : x # xs := by
  cases xs with
  | nil => exact .empty
  | cons y ys =>
      cases h with
      | cons _ hxs => exact distinct_single (distinct_subset hxs Fset.subset_union_left)

/-! ## Derived freshness relations -/

variable {A : Type u} [FiniteSupport A]

/-- Agda: `_##_` (WSLN/Fresh.agda). -/
def DistinctFresh {n : Nat} (xs : Vec Atom n) (a : A) : Prop := Distinct xs (supp a)

@[inherit_doc DistinctFresh]
scoped infix:50 " ## " => WSLN.DistinctFresh

/-- Agda: `_#_#_` (WSLN/Fresh.agda). -/
def Fresh₂ (x y : Atom) (a : A) : Prop :=
  DistinctFresh (Vec.cons y (Vec.cons x Vec.nil)) a

@[inherit_doc Fresh₂]
scoped notation:50 x:51 " # " y:51 " # " a:51 => WSLN.Fresh₂ x y a

/-- Introduce the two-atom freshness evidence `x # y # a`.  The Agda development
builds the `Distinct` telescope `##:: … (##:: … ##◇)` inline. -/
theorem fresh₂Intro {a : A} {x y : Atom} (hy : y # a) (hx : x # a) (hxy : x # y) :
    x # y # a :=
  .cons hy (.cons (.union hxy hx) .nil)

/-- Destructure the two-atom freshness evidence `x # y # a`.  The Agda development
pattern matches on the `Distinct` telescope. -/
theorem fresh₂Inv {a : A} {x y : Atom} (h : x # y # a) : (y # a) ∧ (x # a) ∧ (x # y) :=
  ⟨distinct_cons₂ h, distinct_cons₂ (distinct_cons₁ h),
    fresh_symm (Fset.notMem_union_left (distinct_cons₃ h))⟩

/-- Agda: `_#_#_#_` (WSLN/Fresh.agda). -/
def Fresh₃ (x y z : Atom) (a : A) : Prop :=
  DistinctFresh (Vec.cons z (Vec.cons y (Vec.cons x Vec.nil))) a

@[inherit_doc Fresh₃]
scoped notation:50 x:51 " # " y:51 " # " z:51 " # " a:51 => WSLN.Fresh₃ x y z a

end WSLN

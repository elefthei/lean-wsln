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

class FiniteSupport (A : Type u) where
  supp : A → Fset

export FiniteSupport (supp)

/-- The derived freshness relation. -/
def Fresh {A : Type u} [FiniteSupport A] (x : Atom) (a : A) : Prop :=
  Fset.NotMem x (supp a)

@[inherit_doc Fresh]
scoped infix:50 " # " => WSLN.Fresh

def fresh {A : Type u} [FiniteSupport A] (a : A) : { x : Atom // x # a } :=
  ⟨Fset.new (supp a), Fset.new_notMem (supp a)⟩

instance decidableFresh {A : Type u} [FiniteSupport A] (x : Atom) (a : A) :
    Decidable (x # a) :=
  Fset.decidableNotMem x (supp a)

/-! ## Instances -/

instance instFiniteSupportAtom : FiniteSupport Atom := ⟨fun x => ｛ x ｝⟩

instance instFiniteSupportFset : FiniteSupport Fset := ⟨id⟩

instance instFiniteSupportFin {n : Nat} : FiniteSupport (Fin n) := ⟨fun _ => ∅⟩

instance instFiniteSupportProd {A : Type u} {B : Type v} [FiniteSupport A]
    [FiniteSupport B] : FiniteSupport (A × B) :=
  ⟨fun p => supp p.1 ∪ supp p.2⟩

def suppList {A : Type u} [FiniteSupport A] : List A → Fset
  | [] => ∅
  | a :: as => supp a ∪ suppList as

instance instFiniteSupportList {A : Type u} [FiniteSupport A] : FiniteSupport (List A) :=
  ⟨suppList⟩

def suppVec {A : Type u} [FiniteSupport A] : {n : Nat} → Vec A n → Fset
  | _, .nil => ∅
  | _, .cons a as => supp a ∪ suppVec as

instance instFiniteSupportVec {A : Type u} [FiniteSupport A] {n : Nat} :
    FiniteSupport (Vec A n) :=
  ⟨suppVec⟩

/-- Pick an atom fresh for `a` that also avoids the finite set `S`: `fresh` at a
pair, with the two halves of the freshness split once.  Lean-only, no Agda
counterpart: the Agda development re-splits `fresh ((a , S))` with `∉∪₁`/`∉∪₂` at
every use site. -/
def freshFor {A : Type u} [FiniteSupport A] (a : A) (S : Fset) :
    { x : Atom // (x # a) ∧ (x ∉ᶠ S) } :=
  let f := fresh ((a, S) : A × Fset)
  ⟨f.val, Fset.notMem_union_left f.property, Fset.notMem_union_right f.property⟩

theorem fresh_symm {x y : Atom} (h : x # y) : y # x :=
  .single (Ne.symm (Fset.ne_of_notMem_single h))

/-! ## Freshness for tuples of mutually distinct atoms -/

/-- Cf. A. Charguéraud, *The Locally Nameless Representation*, J. Autom. Reasoning
49 (2012) section 7.1. -/
inductive Distinct : {n : Nat} → Vec Atom n → Fset → Prop where
  | nil {S : Fset} : Distinct Vec.nil S
  | cons {n : Nat} {xs : Vec Atom n} {x : Atom} {S : Fset}
      (hx : x ∉ᶠ S) (hxs : Distinct xs (｛ x ｝ ∪ S)) : Distinct (Vec.cons x xs) S

theorem distinct_subset {n : Nat} {xs : Vec Atom n} {S S' : Fset}
    (h : Distinct xs S') (hs : S ⊆ S') : Distinct xs S := by
  induction h generalizing S with
  | nil => exact .nil
  | @cons n xs x S' hx hxs ih =>
      exact .cons (Fset.subset_notMem hs hx)
        (ih (Fset.union_subset_union Fset.subset_refl hs))

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

theorem distinct_cons₁ {n : Nat} {xs : Vec Atom n} {x : Atom} {S : Fset}
    (h : Distinct (Vec.cons x xs) S) : Distinct xs S := by
  cases h with
  | cons _ hxs => exact distinct_subset hxs Fset.subset_union_right

theorem distinct_cons₂ {n : Nat} {xs : Vec Atom n} {x : Atom} {S : Fset}
    (h : Distinct (Vec.cons x xs) S) : x ∉ᶠ S := by
  cases h with
  | cons hx _ => exact hx

theorem distinct_cons₃ {n : Nat} {xs : Vec Atom n} {x : Atom} {S : Fset}
    (h : Distinct (Vec.cons x xs) S) : x # xs := by
  cases xs with
  | nil => exact .empty
  | cons y ys =>
      cases h with
      | cons _ hxs => exact distinct_single (distinct_subset hxs Fset.subset_union_left)

/-! ## Derived freshness relations -/

variable {A : Type u} [FiniteSupport A]

/-- The atoms `xs` are pairwise distinct and fresh for `a`. -/
def DistinctFresh {n : Nat} (xs : Vec Atom n) (a : A) : Prop := Distinct xs (supp a)

@[inherit_doc DistinctFresh]
scoped infix:50 " ## " => WSLN.DistinctFresh

/-- Two-atom freshness `x # y # a`. -/
def Fresh₂ (x y : Atom) (a : A) : Prop :=
  DistinctFresh (Vec.cons y (Vec.cons x Vec.nil)) a

@[inherit_doc Fresh₂]
scoped notation:50 x:51 " # " y:51 " # " a:51 => WSLN.Fresh₂ x y a

/-- Introduce the two-atom freshness evidence `x # y # a`.  The Agda development
builds the `Distinct` telescope `##:: … (##:: … ##◇)` inline. -/
theorem Fresh₂.intro {a : A} {x y : Atom} (hy : y # a) (hx : x # a) (hxy : x # y) :
    x # y # a :=
  .cons hy (.cons (.union hxy hx) .nil)

/-- Destructure the two-atom freshness evidence `x # y # a`.  The Agda development
pattern matches on the `Distinct` telescope. -/
theorem Fresh₂.inv {a : A} {x y : Atom} (h : x # y # a) : (y # a) ∧ (x # a) ∧ (x # y) :=
  ⟨distinct_cons₂ h, distinct_cons₂ (distinct_cons₁ h),
    fresh_symm (Fset.notMem_union_left (distinct_cons₃ h))⟩

/-- Three-atom freshness `x # y # z # a`. -/
def Fresh₃ (x y z : Atom) (a : A) : Prop :=
  DistinctFresh (Vec.cons z (Vec.cons y (Vec.cons x Vec.nil))) a

@[inherit_doc Fresh₃]
scoped notation:50 x:51 " # " y:51 " # " z:51 " # " a:51 => WSLN.Fresh₃ x y z a

end WSLN

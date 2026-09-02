import WSLN.Index

/-!
# Atomic names and finite sets of atoms

Port of `agda-code/agda/WSLN/Atom.agda`.

The Agda module's inductive atom inequality `_≠𝔸_` and its proof-irrelevance
machinery (`isProp≠𝔸`, `≠𝔸irrefl`, `≠𝔸symm`, `≢→≠𝔸`, `≠𝔸→≢`, `dec≠𝔸`) are dropped:
in Lean `x ≠ y` is already a proposition, symmetric via `Ne.symm`, decidable via
`instDecidableEqNat`; Agda's `1+≠𝔸` is `Nat.succ_ne_self`.

Membership `_∈𝔸_` and non-membership `_∉𝔸_` are kept as inductive families, since
the development pattern-matches on non-membership evidence pervasively.  `NotMem`
is written `x ∉ᶠ s` to distinguish it from Lean's `x ∉ s` (which is `¬ (x ∈ s)`);
`Fset.notMem_of_not_mem` / `Fset.not_mem_of_notMem` are the two bridges (Agda
`¬∈→∉` / `∉→¬∈`).
-/

namespace WSLN

/-! ## Atomic names -/

/-- Atomic names are natural numbers. -/
abbrev Atom := Nat

/-! ## Finite sets of atoms -/

inductive Fset : Type where
  | empty : Fset
  /-- The singleton set `｛ x ｝`. -/
  | single : Atom → Fset
  | union : Fset → Fset → Fset
  deriving DecidableEq, Repr

instance : EmptyCollection Fset := ⟨Fset.empty⟩
instance : Union Fset := ⟨Fset.union⟩
instance : Singleton Atom Fset := ⟨Fset.single⟩
instance : Insert Atom Fset := ⟨fun x s => Fset.union (Fset.single x) s⟩
instance : Inhabited Fset := ⟨Fset.empty⟩

@[inherit_doc Fset.single]
scoped notation "｛" x "｝" => Fset.single x

namespace Fset

theorem union_inj {s s' t t' : Fset} (e : s ∪ t = s' ∪ t') : s = s' ∧ t = t' := by
  cases e; exact ⟨rfl, rfl⟩

def bigUnion (f : Atom → Fset) : Fset → Fset
  | .empty => ∅
  | .single x => f x
  | .union s t => bigUnion f s ∪ bigUnion f t

/-! ## Membership -/

inductive Mem (x : Atom) : Fset → Prop where
  | single : Mem x ｛ x ｝
  | unionL {s t : Fset} : Mem x s → Mem x (s ∪ t)
  | unionR {s t : Fset} : Mem x t → Mem x (s ∪ t)

instance : Membership Atom Fset := ⟨fun s x => Mem x s⟩

/-- Non-membership `x ∉ᶠ s`, as an inductive predicate. -/
inductive NotMem (x : Atom) : Fset → Prop where
  | empty : NotMem x ∅
  | single {y : Atom} : x ≠ y → NotMem x ｛ y ｝
  | union {s t : Fset} : NotMem x s → NotMem x t → NotMem x (s ∪ t)

end Fset

@[inherit_doc WSLN.Fset.NotMem]
scoped infix:50 " ∉ᶠ " => WSLN.Fset.NotMem

namespace Fset

theorem ne_of_notMem_single {x y : Atom} (h : x ∉ᶠ ｛ y ｝) : x ≠ y := by
  cases h with | single p => exact p

theorem notMem_union_left {x : Atom} {s t : Fset} (h : x ∉ᶠ s ∪ t) : x ∉ᶠ s := by
  cases h with | union p _ => exact p

theorem notMem_union_right {x : Atom} {s t : Fset} (h : x ∉ᶠ s ∪ t) : x ∉ᶠ t := by
  cases h with | union _ p => exact p

theorem not_mem_of_notMem {x : Atom} {s : Fset} (h : x ∉ᶠ s) : ¬ (x ∈ s) := by
  induction h with
  | empty => intro p; cases p
  | single hne => intro p; cases p; exact hne rfl
  | union _ _ ih ih' =>
      intro p
      cases p with
      | unionL q => exact ih q
      | unionR q => exact ih' q

theorem notMem_of_not_mem {x : Atom} {s : Fset} (h : ¬ (x ∈ s)) : x ∉ᶠ s := by
  induction s with
  | empty => exact .empty
  | single y => refine .single ?_; intro e; subst e; exact h Mem.single
  | union s t ihs iht =>
      exact .union (ihs fun p => h (Mem.unionL p)) (iht fun p => h (Mem.unionR p))

/-- Decidability of membership; used by Agda's `dec∉`. -/
instance decidableMem (x : Atom) (s : Fset) : Decidable (x ∈ s) :=
  match s with
  | .empty => isFalse (fun p => by cases p)
  | .single y =>
      if h : x = y then isTrue (by subst h; exact Mem.single)
      else isFalse (fun p => by cases p; exact h rfl)
  | .union s t =>
      match decidableMem x s, decidableMem x t with
      | isTrue p, _ => isTrue (Mem.unionL p)
      | _, isTrue q => isTrue (Mem.unionR q)
      | isFalse p, isFalse q =>
          isFalse fun r => by
            cases r with
            | unionL r => exact p r
            | unionR r => exact q r

instance decidableNotMem (x : Atom) (s : Fset) : Decidable (x ∉ᶠ s) :=
  if h : x ∈ s then isFalse (fun p => not_mem_of_notMem p h)
  else isTrue (notMem_of_not_mem h)

/-! ## Finite inexhaustibility -/

def maxfs : Fset → Atom
  | .empty => 0
  | .single x => x
  | .union s t => max (maxfs s) (maxfs t)

theorem le_maxfs {x : Atom} {s : Fset} (h : x ∈ s) : x ≤ maxfs s := by
  induction h with
  | single => exact Nat.le_refl _
  | unionL p ih => exact Nat.le_trans ih (Nat.le_max_left _ _)
  | unionR p ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

def new (s : Fset) : Atom := maxfs s + 1

theorem new_notMem (s : Fset) : new s ∉ᶠ s :=
  notMem_of_not_mem fun h => Nat.not_succ_le_self (maxfs s) (le_maxfs h)

/-! ## Membership and non-membership, in `simp`-normal form

These have no Agda counterpart; they replace the Agda development's point-free
manipulation of `∈`/`∉`/`⊆` witnesses by ordinary `simp` reasoning. -/

@[simp] theorem mem_empty_iff {x : Atom} : x ∈ (∅ : Fset) ↔ False := by
  constructor
  · intro h; cases h
  · intro h; exact h.elim

@[simp] theorem mem_single_iff {x y : Atom} : x ∈ ｛ y ｝ ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; exact Mem.single

@[simp] theorem mem_union_iff {x : Atom} {s t : Fset} : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  constructor
  · intro h
    cases h with
    | unionL p => exact .inl p
    | unionR p => exact .inr p
  · intro h; exact h.elim Mem.unionL Mem.unionR

@[simp] theorem notMem_empty_iff {x : Atom} : (x ∉ᶠ (∅ : Fset)) ↔ True :=
  ⟨fun _ => trivial, fun _ => .empty⟩

@[simp] theorem notMem_single_iff {x y : Atom} : (x ∉ᶠ ｛ y ｝) ↔ x ≠ y :=
  ⟨ne_of_notMem_single, NotMem.single⟩

@[simp] theorem notMem_union_iff {x : Atom} {s t : Fset} :
    (x ∉ᶠ s ∪ t) ↔ ((x ∉ᶠ s) ∧ (x ∉ᶠ t)) :=
  ⟨fun h => ⟨notMem_union_left h, notMem_union_right h⟩, fun h => .union h.1 h.2⟩

/-! ## Containment -/

def Subset (s t : Fset) : Prop := ∀ ⦃x : Atom⦄, x ∈ s → x ∈ t

instance : HasSubset Fset := ⟨Subset⟩

theorem subset_refl {s : Fset} : s ⊆ s := fun _ h => h

theorem subset_trans {s t u : Fset} (h : s ⊆ t) (h' : t ⊆ u) : s ⊆ u :=
  fun _ p => h' (h p)

theorem union_subset {s t u : Fset} (h : s ⊆ u) (h' : t ⊆ u) : s ∪ t ⊆ u := by
  intro x p
  cases p with
  | unionL q => exact h q
  | unionR q => exact h' q

theorem union_subset_union {s s' t t' : Fset} (h : s ⊆ s') (h' : t ⊆ t') :
    s ∪ t ⊆ s' ∪ t' :=
  union_subset (fun _ p => Mem.unionL (h p)) (fun _ p => Mem.unionR (h' p))

theorem subset_union_left {s t : Fset} : s ⊆ s ∪ t := fun _ p => Mem.unionL p

theorem subset_union_right {s t : Fset} : t ⊆ s ∪ t := fun _ p => Mem.unionR p

@[simp] theorem empty_subset {s : Fset} : (∅ : Fset) ⊆ s := fun _ h => nomatch h

@[simp] theorem union_subset_iff {s t u : Fset} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  ⟨fun h => ⟨fun _ p => h (Mem.unionL p), fun _ p => h (Mem.unionR p)⟩,
   fun h => union_subset h.1 h.2⟩

@[simp] theorem single_subset_iff {x : Atom} {u : Fset} : ｛ x ｝ ⊆ u ↔ x ∈ u :=
  ⟨fun h => h Mem.single, fun h _ p => by cases p; exact h⟩

theorem subset_bigUnion {x : Atom} {s : Fset} (f : Atom → Fset) (h : x ∈ s) :
    f x ⊆ bigUnion f s := by
  induction h with
  | single => exact fun _ p => p
  | unionL _ ih => exact fun _ p => Mem.unionL (ih p)
  | unionR _ ih => exact fun _ p => Mem.unionR (ih p)

theorem subset_notMem {s t : Fset} {x : Atom} (h : s ⊆ t) (h' : x ∉ᶠ t) : x ∉ᶠ s :=
  notMem_of_not_mem fun p => not_mem_of_notMem h' (h p)

theorem mem_left_of_notMem_right {x : Atom} {s t : Fset} (h : x ∈ s ∪ t) (h' : x ∉ᶠ t) :
    x ∈ s := by
  cases h with
  | unionL p => exact p
  | unionR p => exact absurd p (not_mem_of_notMem h')

theorem mem_right_of_notMem_left {x : Atom} {s t : Fset} (h : x ∈ s ∪ t) (h' : x ∉ᶠ s) :
    x ∈ t := by
  cases h with
  | unionL p => exact absurd p (not_mem_of_notMem h')
  | unionR p => exact p

theorem notMem_subset {s t : Fset} {x : Atom} (h : x ∉ᶠ t) (h' : t ⊆ s ∪ ｛ x ｝) :
    t ⊆ s := by
  intro y hy
  cases h' hy with
  | unionL p => exact p
  | unionR p => cases p; exact absurd hy (not_mem_of_notMem h)

end Fset

/-! ## Name swapping -/

/-- The transposition `x ≀ y`: swaps the two atoms and fixes every other. -/
def swap (x y : Atom) : Atom → Atom :=
  fun z => if x = z then y else if y = z then x else z

@[inherit_doc swap]
scoped infix:60 " ≀ " => WSLN.swap

end WSLN

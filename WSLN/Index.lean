import WSLN.Prelude

/-!
# Scopes and de Bruijn indices

Port of `agda-code/agda/WSLN/Index.agda`.

A *scope* is a natural number: the number of de Bruijn indices in scope.  A scoped
set is a `Nat`-indexed family together with weakening operations, i.e. a covariant
presheaf on `(Nat, ≤)`.  Because `Nat.le` proofs are propositions, the weakening
laws are stated for arbitrary ordering proofs.

The Agda module's inductive index inequality `_≠i_` and the associated proof
irrelevance machinery (`isProp≠`, `removeIrrel`) are dropped: Lean's `Prop` is
proof irrelevant, so `i ≠ j` already is a proposition and `removeIrrel` is `rfl`.
Agda `Fin`, `actFin`, `suc^`, `toℕ`, `decFin` map onto core `Fin`, `Fin.castLE`,
`Fin.natAdd`, `Fin.val`, `instDecidableEqFin`.
-/

namespace WSLN

universe u

/-! ## Scoped sets -/

/-- Agda: `Scoped` (WSLN/Index.agda).

A family `A : Nat → Type` is *scoped* when it is a covariant presheaf for `≤`. -/
class Scoped (A : Nat → Type u) where
  /-- Agda: `_‿_`. Scope weakening. -/
  weaken : {m : Nat} → A m → (n : Nat) → m ≤ n → A n
  /-- Agda: `‿unit`. -/
  weaken_self : ∀ {n : Nat} (x : A n) (h : n ≤ n), weaken x n h = x
  /-- Agda: `‿assoc`. -/
  weaken_trans : ∀ {k : Nat} (x : A k) (m n : Nat) (h₁ : k ≤ m) (h₂ : m ≤ n) (h₃ : k ≤ n),
    weaken (weaken x m h₁) n h₂ = weaken x n h₃

/-! ## Indices

Agda's `toℕ` is `Fin.val`, `toℕ<` is `Fin.isLt`, `toℕInj` is `Fin.ext`, `toℕ‿` is
core's `Fin.val_castLE`, and `decFin` / `hasDecEqFin` are core's
`instDecidableEqFin`.  The `Scoped Fin` instance fields `unitFin`/`assocFin` are the
`weaken_self`/`weaken_trans` fields of `instScopedFin` below.  The inductive index
inequality `_≠i_` and its companions `sucInj`, `suc≢`, `suc≠`, `≠iirrefl`, `≢→≠i`,
`isProp≠`, `removeIrrel` are dropped: `i ≠ j` is already a proposition in Lean. -/

/-- Agda: `suc^{m}` / `toℕ∘suc^` (WSLN/Index.agda).

Shifts an outer index past `m` newly bound indices.  Agda's `Arg[ n ](m :: ms)`
stores a `Trm[ m + n ]`; here the summands are swapped to `Trm Sg (n + m)`, so that
`n + 0` reduces to `n` for a *variable* `n`.  That makes an arity-`0` argument
literally a `Trm Sg n` and an arity-`1` argument literally a `Trm Sg (n + 1)`. -/
def shiftIdx (m : Nat) {n : Nat} (i : Fin n) : Fin (n + m) :=
  ⟨m + i.val, by have := i.isLt; omega⟩

@[simp] theorem val_shiftIdx (m : Nat) {n : Nat} (i : Fin n) :
    (shiftIdx m i).val = m + i.val := rfl

/-- `Fin.cast` is injective (used to transport index disequalities). -/
theorem cast_ne {m n : Nat} (e : m = n) {i j : Fin m} (h : i ≠ j) :
    Fin.cast e i ≠ Fin.cast e j :=
  fun heq => h (Fin.ext (congrArg (Fin.val (n := n)) heq))

/-- Agda: `ScopedFin` (WSLN/Index.agda); `actFin` is `Fin.castLE`. -/
instance instScopedFin : Scoped Fin where
  weaken i _ h := Fin.castLE h i
  weaken_self _ _ := rfl
  weaken_trans _ _ _ _ _ _ := rfl

@[simp] theorem weaken_fin {m n : Nat} (i : Fin m) (h : m ≤ n) :
    Scoped.weaken i n h = Fin.castLE h i := rfl

/-! ## Removing and inserting indices -/

/-- Agda: `remove` (WSLN/Index.agda).

Removes the index `i` from `Fin (n+1)`, mapping the remaining indices back into
`Fin n` while preserving their order. -/
def remove {n : Nat} (i j : Fin (n + 1)) (h : i ≠ j) : Fin n :=
  ⟨if j.val < i.val then j.val else j.val - 1, by
    have h1 := i.isLt
    have h2 := j.isLt
    have h3 : i.val ≠ j.val := fun e => h (Fin.ext e)
    split <;> omega⟩

/-- Agda: `insert` (WSLN/Index.agda).

Injects `Fin n` into `Fin (n+1)` avoiding the index `i`. -/
def insert {n : Nat} (i : Fin (n + 1)) (j : Fin n) : Fin (n + 1) :=
  ⟨if j.val < i.val then j.val else j.val + 1, by
    have h2 := j.isLt
    split <;> omega⟩

@[simp] theorem remove_val {n : Nat} (i j : Fin (n + 1)) (h : i ≠ j) :
    (remove i j h).val = if j.val < i.val then j.val else j.val - 1 := rfl

@[simp] theorem insert_val {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    (insert i j).val = if j.val < i.val then j.val else j.val + 1 := rfl

/-- Agda: `insertAvoids` (WSLN/Index.agda). -/
theorem insertAvoids {n : Nat} (i : Fin (n + 1)) (j : Fin n) : i ≠ insert i j := by
  intro e
  have hv := congrArg Fin.val e
  simp only [insert_val] at hv
  split at hv <;> omega

/-- Agda: `removeInsert` (WSLN/Index.agda). -/
theorem removeInsert {n : Nat} (i : Fin (n + 1)) (j : Fin n) (h : i ≠ insert i j) :
    remove i (insert i j) h = j := by
  apply Fin.ext
  by_cases hj : j.val < i.val
  · simp [hj]
  · have h2 : ¬ (j.val + 1 < i.val) := by omega
    simp [hj, h2]

/-- Agda: `insertRemove` (WSLN/Index.agda). -/
theorem insertRemove {n : Nat} (i j : Fin (n + 1)) (h : i ≠ j) :
    insert i (remove i j h) = j := by
  have h3 : i.val ≠ j.val := fun e => h (Fin.ext e)
  have h4 := j.isLt
  apply Fin.ext
  by_cases hj : j.val < i.val
  · simp [hj]
  · have h5 : ¬ (j.val - 1 < i.val) := by omega
    simp [hj, h5]
    omega

/-- Agda: `remove<` (WSLN/Index.agda). -/
theorem remove_lt {n : Nat} (i : Fin (n + 1)) (j : Fin n)
    (h : i ≠ Fin.castLE (Nat.le_succ n) j) (hlt : j.val < i.val) :
    remove i (Fin.castLE (Nat.le_succ n) j) h = j := by
  apply Fin.ext
  simp [hlt]

/-- Agda: `insert<` (WSLN/Index.agda). -/
theorem insert_lt {m n : Nat} (i : Fin (n + 1)) (j : Fin m) (h : m ≤ n) (h' : m ≤ n + 1)
    (hlt : j.val < i.val) :
    insert i (Fin.castLE h j) = Fin.castLE h' j := by
  apply Fin.ext
  simp [hlt]

end WSLN

import WSLN.Concretion

/-!
# Closing and abstraction

Port of `agda-code/agda/WSLN/Sig/Abstraction.agda`.

`cls`/`clsArg` use the same equation trick as `opn`: the scope equation
`n = m + 1` is an explicit argument, since closing under a binder of depth `k`
needs `k + n = (k + m) + 1`.

Agda's `opnFin≢` (which only existed to apply `removeIrrel`) is subsumed by
`opn_var_ne`: index disequality proofs are irrelevant in Lean.
-/

namespace WSLN

/-! ## Name closing -/

mutual

/-- Agda: `cls` (WSLN/Sig/Abstraction.agda).

Name closing combined with `insert`, giving an operation `Trm Sg m → Trm Sg (m+1)`. -/
def cls {Sg : Sig} {m n : Nat} (x : Atom) (i : Fin n) (t : Trm Sg m) (e : n = m + 1) :
    Trm Sg n :=
  match t with
  | .var j => .var (Fin.cast e.symm (insert (Fin.cast e i) j))
  | .atom y => if x = y then .var i else .atom y
  | .op o ts => .op o (clsArg x i ts e)

/-- Agda: `cls'` (WSLN/Sig/Abstraction.agda). -/
def clsArg {Sg : Sig} {m n : Nat} {ms : List Nat} (x : Atom) (i : Fin n)
    (ts : Arg Sg m ms) (e : n = m + 1) : Arg Sg n ms :=
  match ts with
  | .nil => .nil
  | .cons (m := k) t us => .cons (cls x (shiftIdx k i) t (by omega)) (clsArg x i us e)

end

@[simp] theorem cls_var {Sg : Sig} {m n : Nat} (x : Atom) (i : Fin n) (j : Fin m)
    (e : n = m + 1) :
    cls x i (.var j : Trm Sg m) e = .var (Fin.cast e.symm (insert (Fin.cast e i) j)) := rfl

theorem cls_atom {Sg : Sig} {m n : Nat} (x : Atom) (i : Fin n) (y : Atom)
    (e : n = m + 1) :
    cls x i (.atom y : Trm Sg m) e = if x = y then .var i else .atom y := rfl

@[simp] theorem cls_atom_eq {Sg : Sig} {m n : Nat} (x : Atom) (i : Fin n)
    (e : n = m + 1) : cls x i (.atom x : Trm Sg m) e = .var i := by
  rw [cls_atom]; simp

theorem cls_atom_ne {Sg : Sig} {m n : Nat} {x y : Atom} (i : Fin n) (e : n = m + 1)
    (h : x ≠ y) : cls x i (.atom y : Trm Sg m) e = .atom y := by
  rw [cls_atom]; simp [h]

@[simp] theorem cls_op {Sg : Sig} {m n : Nat} (x : Atom) (i : Fin n) (o : Sg.Op)
    (ts : Arg Sg m (Sg.ar o)) (e : n = m + 1) :
    cls x i (.op o ts) e = .op o (clsArg x i ts e) := rfl

@[simp] theorem clsArg_nil {Sg : Sig} {m n : Nat} (x : Atom) (i : Fin n)
    (e : n = m + 1) : clsArg x i (Arg.nil : Arg Sg m []) e = .nil := rfl

@[simp] theorem clsArg_cons {Sg : Sig} {m n k : Nat} {ms : List Nat} (x : Atom)
    (i : Fin n) (t : Trm Sg (m + k)) (us : Arg Sg m ms) (e : n = m + 1) :
    clsArg x i (Arg.cons t us) e
      = .cons (cls x (shiftIdx k i) t (by omega)) (clsArg x i us e) := rfl

/-- Agda: `_<~_` (WSLN/Sig/Abstraction.agda). -/
def Trm.close {Sg : Sig} {m : Nat} (i : Fin (m + 1)) (x : Atom) (t : Trm Sg m) :
    Trm Sg (m + 1) := cls x i t rfl

/-- Agda: `_<~'_` (WSLN/Sig/Abstraction.agda). -/
def Arg.close {Sg : Sig} {m : Nat} {ms : List Nat} (i : Fin (m + 1)) (x : Atom)
    (ts : Arg Sg m ms) : Arg Sg (m + 1) ms := clsArg x i ts rfl

/-! ## Abstraction -/

/-- Agda: `_．_` (WSLN/Sig/Abstraction.agda).

The usual notion of abstraction: the `i = zero` case of closing.  Note that
`cls x zero` may call `cls x i` for nonzero `i`, hence the general definition. -/
def Trm.abs {Sg : Sig} {n : Nat} (x : Atom) (t : Trm Sg n) : Trm Sg (n + 1) :=
  cls x ⟨0, Nat.succ_pos n⟩ t rfl

@[inherit_doc Trm.abs] scoped infixr:2 " ． " => WSLN.Trm.abs

/-! ## Concreting abstractions -/

mutual

/-- Agda: `opnCls` (WSLN/Sig/Abstraction.agda). -/
theorem opnCls {Sg : Sig} {m n : Nat} (x : Atom) (i : Fin n) (t : Trm Sg m)
    (e : n = m + 1) (b : Trm Sg 0) : opn i b (cls x i t e) e = (x ≔ b) * t := by
  match t with
  | .var j =>
      have hav : Fin.cast e i ≠ insert (Fin.cast e i) j := insertAvoids _ _
      have hne : i ≠ Fin.cast e.symm (insert (Fin.cast e i) j) := by
        intro he
        exact hav (Fin.ext (congrArg (Fin.val (n := n)) he))
      rw [cls_var, opn_var_ne b e hne, actSb_var]
      refine congrArg Trm.var (Fin.ext ?_)
      simp only [remove_val, Fin.val_cast, insert_val]
      by_cases hj : j.val < i.val
      · simp [hj]
      · have h2 : ¬ (j.val + 1 < i.val) := by omega
        simp [hj, h2]
  | .atom y =>
      by_cases h : x = y
      · subst h
        rw [cls_atom_eq, opn_var_eq, actSb_atom, Sb.single_eq]
      · rw [cls_atom_ne i e h, opn_atom, actSb_atom, Sb.single_neq _ h]
        simp [Sb.id]
  | .op o ts => simpa using opnClsArg x i ts e b

/-- Agda: `opnCls'` (WSLN/Sig/Abstraction.agda). -/
theorem opnClsArg {Sg : Sig} {m n : Nat} {ms : List Nat} (x : Atom) (i : Fin n)
    (ts : Arg Sg m ms) (e : n = m + 1) (b : Trm Sg 0) :
    opnArg i b (clsArg x i ts e) e = (x ≔ b) * ts := by
  match ts with
  | .nil => rfl
  | .cons (m := k) t us =>
      simp only [clsArg_cons, opnArg_cons, actSb_cons, Arg.cons.injEq]
      exact ⟨opnCls x (shiftIdx k i) t (by omega) b, opnClsArg x i us e b⟩

end

/-- Agda: `concAbs` (WSLN/Sig/Abstraction.agda). -/
theorem concAbs {Sg : Sig} {n : Nat} (x : Atom) (t : Trm Sg n) (b : Trm Sg 0) :
    (x ． t)[b] = (x ≔ b) * t := opnCls x _ t rfl b

/-- Agda: `concAbs'` (WSLN/Sig/Abstraction.agda). -/
theorem concAbs' {Sg : Sig} {n : Nat} (x : Atom) (t : Trm Sg n) : (x ． t)[x] = t := by
  rw [conc_atom, ← conc_trm, concAbs x t (Trm.atom x), updateIdSb]

/-! ## Abstracting concretions -/

mutual

/-- Agda: `clsOpn` (WSLN/Sig/Abstraction.agda). -/
theorem clsOpn {Sg : Sig} {m n : Nat} (x : Atom) (i : Fin m) (t : Trm Sg m)
    (e : m = n + 1) (h : x # t) : cls x i (opn i (Trm.atom x) t e) e = t := by
  match t with
  | .var j =>
      by_cases hij : i = j
      · subst hij
        rw [opn_var_eq, Trm.weaken_atom, cls_atom_eq]
      · rw [opn_var_ne (Trm.atom x) e hij, cls_var]
        refine congrArg Trm.var (Fin.ext ?_)
        have hv : i.val ≠ j.val := fun ev => hij (Fin.ext ev)
        have hj := j.isLt
        simp only [Fin.val_cast, insert_val, remove_val]
        by_cases hlt : j.val < i.val
        · simp [hlt]
        · have h2 : ¬ (j.val - 1 < i.val) := by omega
          simp [hlt, h2]
          omega
  | .atom y =>
      rw [opn_atom, cls_atom_ne i e (Fset.ne_of_notMem_single h)]
  | .op o ts => simpa using clsOpnArg x i ts e h

/-- Agda: `clsOpn'` (WSLN/Sig/Abstraction.agda). -/
theorem clsOpnArg {Sg : Sig} {m n : Nat} {ms : List Nat} (x : Atom) (i : Fin m)
    (ts : Arg Sg m ms) (e : m = n + 1) (h : x # ts) :
    clsArg x i (opnArg i (Trm.atom x) ts e) e = ts := by
  match ts with
  | .nil => rfl
  | .cons (m := k) t us =>
      simp only [opnArg_cons, clsArg_cons, Arg.cons.injEq]
      exact ⟨clsOpn x (shiftIdx k i) t (by omega) (Fset.notMem_union_left h),
        clsOpnArg x i us e (Fset.notMem_union_right h)⟩

end

/-- Agda: `absConc` (WSLN/Sig/Abstraction.agda). -/
theorem absConc {Sg : Sig} {n : Nat} (x : Atom) (t : Trm Sg (n + 1)) (h : x # t) :
    (x ． t[x]) = t := clsOpn x _ t rfl h

/-! ## Abstracting a fresh name -/

mutual

/-- Agda: `cls#` (WSLN/Sig/Abstraction.agda). -/
theorem cls_fresh_weaken {Sg : Sig} {k m n : Nat} (x : Atom) (i : Fin n) (e : n = m + 1)
    (q : k ≤ i.val) (h₁ : k ≤ m) (h₂ : k ≤ n) (t : Trm Sg k) (h : x # t) :
    cls x i (t.weaken m h₁) e = t.weaken n h₂ := by
  match t with
  | .var j =>
      have hj := j.isLt
      rw [Trm.weaken_var, cls_var, Trm.weaken_var]
      refine congrArg Trm.var (Fin.ext ?_)
      simp only [Fin.val_cast, insert_val, Fin.val_castLE]
      rw [if_pos (by omega : j.val < i.val)]
  | .atom y =>
      rw [Trm.weaken_atom, cls_atom_ne i e (Fset.ne_of_notMem_single h), Trm.weaken_atom]
  | .op o ts => simpa using clsArg_fresh_weaken x i e q h₁ h₂ ts h

/-- Agda: `cls#'` (WSLN/Sig/Abstraction.agda). -/
theorem clsArg_fresh_weaken {Sg : Sig} {k m n : Nat} {ms : List Nat} (x : Atom)
    (i : Fin n) (e : n = m + 1) (q : k ≤ i.val) (h₁ : k ≤ m) (h₂ : k ≤ n)
    (ts : Arg Sg k ms) (h : x # ts) :
    clsArg x i (ts.weaken m h₁) e = ts.weaken n h₂ := by
  match ts with
  | .nil => rfl
  | .cons (m := j) t us =>
      simp only [Arg.weaken_cons, clsArg_cons, Arg.cons.injEq]
      refine ⟨?_, clsArg_fresh_weaken x i e q h₁ h₂ us (Fset.notMem_union_right h)⟩
      exact cls_fresh_weaken x (shiftIdx j i) (by omega)
        (by simp only [val_shiftIdx]; omega) (by omega) (by omega) t
        (Fset.notMem_union_left h)

end

/-- Agda: `abs#` (WSLN/Sig/Abstraction.agda). -/
theorem abs_fresh_weaken {Sg : Sig} (x : Atom) (t : Trm Sg 0) (h : x # t) :
    (x ． t) = t.weaken 1 (Nat.zero_le 1) := by
  have e := cls_fresh_weaken x (⟨0, Nat.succ_pos 0⟩ : Fin 1) rfl (Nat.zero_le _)
    (Nat.zero_le 0) (Nat.zero_le 1) t h
  simp only [Trm.weaken_self] at e
  exact e

/-! ## Finite support properties of abstraction -/

mutual

/-- Agda: `suppCls` (WSLN/Sig/Abstraction.agda). -/
theorem suppCls {Sg : Sig} {m n : Nat} (x : Atom) (i : Fin n) (t : Trm Sg m)
    (e : n = m + 1) : supp (cls x i t e) ⊆ supp t := by
  match t with
  | .var j => intro y hy; rw [cls_var] at hy; cases hy
  | .atom z =>
      intro y hy
      by_cases h : x = z
      · subst h; rw [cls_atom_eq] at hy; cases hy
      · rw [cls_atom_ne i e h] at hy; exact hy
  | .op o ts => intro y hy; exact suppClsArg x i ts e hy

/-- Agda: `suppCls'` (WSLN/Sig/Abstraction.agda). -/
theorem suppClsArg {Sg : Sig} {m n : Nat} {ms : List Nat} (x : Atom) (i : Fin n)
    (ts : Arg Sg m ms) (e : n = m + 1) : supp (clsArg x i ts e) ⊆ supp ts := by
  match ts with
  | .nil => intro y hy; cases hy
  | .cons (m := k) t us =>
      intro y hy
      simp only [clsArg_cons, supp_cons] at hy
      cases hy with
      | unionL p => exact .unionL (suppCls x (shiftIdx k i) t (by omega) p)
      | unionR p => exact .unionR (suppClsArg x i us e p)

end

/-- Agda: `suppAbs` (WSLN/Sig/Abstraction.agda). -/
theorem suppAbs {Sg : Sig} {n : Nat} (x : Atom) (t : Trm Sg n) : supp (x ． t) ⊆ supp t :=
  suppCls x _ t rfl

mutual

/-- Agda: `#cls` (WSLN/Sig/Abstraction.agda). -/
theorem fresh_cls {Sg : Sig} {m n : Nat} (x : Atom) (i : Fin n) (t : Trm Sg m)
    (e : n = m + 1) : x # cls x i t e := by
  match t with
  | .var j => rw [cls_var]; exact .empty
  | .atom y =>
      by_cases h : x = y
      · subst h; rw [cls_atom_eq]; exact .empty
      · rw [cls_atom_ne i e h]; exact .single h
  | .op o ts => exact fresh_clsArg x i ts e

/-- Agda: `#cls'` (WSLN/Sig/Abstraction.agda). -/
theorem fresh_clsArg {Sg : Sig} {m n : Nat} {ms : List Nat} (x : Atom) (i : Fin n)
    (ts : Arg Sg m ms) (e : n = m + 1) : x # clsArg x i ts e := by
  match ts with
  | .nil => exact .empty
  | .cons (m := k) t us =>
      simp only [clsArg_cons]
      exact .union (fresh_cls x (shiftIdx k i) t (by omega)) (fresh_clsArg x i us e)

end

/-- Agda: `#abs` (WSLN/Sig/Abstraction.agda). -/
theorem fresh_abs {Sg : Sig} {n : Nat} (x : Atom) (t : Trm Sg n) : x # (x ． t) :=
  fresh_cls x _ t rfl

mutual

/-- Agda: `#cls≠` (WSLN/Sig/Abstraction.agda). -/
theorem fresh_cls_ne {Sg : Sig} {m n : Nat} {x y : Atom} (i : Fin n) (t : Trm Sg m)
    (e : n = m + 1) (h : y # (x, t)) : y # cls x i t e := by
  match t with
  | .var j => rw [cls_var]; exact .empty
  | .atom z =>
      by_cases hx : x = z
      · subst hx; rw [cls_atom_eq]; exact .empty
      · rw [cls_atom_ne i e hx]; exact Fset.notMem_union_right h
  | .op o ts => exact fresh_clsArg_ne i ts e h

/-- Agda: `#cls'≠` (WSLN/Sig/Abstraction.agda). -/
theorem fresh_clsArg_ne {Sg : Sig} {m n : Nat} {ms : List Nat} {x y : Atom} (i : Fin n)
    (ts : Arg Sg m ms) (e : n = m + 1) (h : y # (x, ts)) : y # clsArg x i ts e := by
  match ts with
  | .nil => exact .empty
  | .cons (m := k) t us =>
      have hx : y ∉ᶠ supp x := Fset.notMem_union_left h
      have hts := Fset.notMem_union_right h
      simp only [clsArg_cons]
      exact .union
        (fresh_cls_ne (shiftIdx k i) t (by omega)
          (.union hx (Fset.notMem_union_left hts)))
        (fresh_clsArg_ne i us e (.union hx (Fset.notMem_union_right hts)))

end

/-- Agda: `#abs'` (WSLN/Sig/Abstraction.agda). -/
theorem fresh_abs' {Sg : Sig} {n : Nat} {x y : Atom} (t : Trm Sg n) (h : y # t) :
    y # (x ． t) := by
  by_cases hxy : x = y
  · subst hxy; exact fresh_abs x t
  · exact fresh_cls_ne _ t rfl (.union (.single (Ne.symm hxy)) h)

/-- Agda: `y#x．𝐚x` (WSLN/Sig/Abstraction.agda). -/
theorem fresh_abs_atom {Sg : Sig} (x y : Atom) : y # (x ． (Trm.atom x : Trm Sg 0)) := by
  by_cases h : x = y
  · subst h; exact fresh_abs x _
  · exact fresh_abs' (x := x) (Trm.atom x) (.single (Ne.symm h))

/-! ## Action of substitutions and renamings on abstractions -/

mutual

/-- Agda: `sbCls` (WSLN/Sig/Abstraction.agda). -/
theorem sbCls {Sg : Sig} {m n : Nat} (σ : Sb Sg) (x x' : Atom) (i : Fin n)
    (t : Trm Sg m) (f : ∀ y, y ∈ supp t → ¬ (x = y) → x' # σ y) (e : n = m + 1) :
    σ * (cls x i t e) = cls x' i ((σ ∘/ x ≔ (Trm.atom x' : Trm Sg 0)) * t) e := by
  match t with
  | .var j => rw [cls_var, actSb_var, actSb_var, cls_var]
  | .atom y =>
      by_cases h : x = y
      · subst h
        rw [cls_atom_eq, actSb_var, actSb_atom, Sb.update_eq, Trm.weaken_atom,
          cls_atom_eq]
      · rw [cls_atom_ne i e h, actSb_atom, actSb_atom, Sb.update_neq _ _ h]
        exact (cls_fresh_weaken x' i e (Nat.zero_le _) (Nat.zero_le m) (Nat.zero_le n)
          (σ y) (f y Fset.Mem.single h)).symm
  | .op o ts => simpa using sbClsArg σ x x' i ts f e

/-- Agda: `sbCls'` (WSLN/Sig/Abstraction.agda). -/
theorem sbClsArg {Sg : Sig} {m n : Nat} {ms : List Nat} (σ : Sb Sg) (x x' : Atom)
    (i : Fin n) (ts : Arg Sg m ms)
    (f : ∀ y, y ∈ supp ts → ¬ (x = y) → x' # σ y) (e : n = m + 1) :
    σ * (clsArg x i ts e) = clsArg x' i ((σ ∘/ x ≔ (Trm.atom x' : Trm Sg 0)) * ts) e := by
  match ts with
  | .nil => rfl
  | .cons (m := k) t us =>
      simp only [clsArg_cons, actSb_cons, Arg.cons.injEq]
      exact ⟨sbCls σ x x' (shiftIdx k i) t
          (fun y hy => f y (Fset.Mem.unionL hy)) (by omega),
        sbClsArg σ x x' i us (fun y hy => f y (Fset.Mem.unionR hy)) e⟩

end

/-- Agda: `sbAbs` (WSLN/Sig/Abstraction.agda). -/
theorem sbAbs {Sg : Sig} {m : Nat} (σ : Sb Sg) (x x' : Atom) (t : Trm Sg m)
    (f : ∀ y, y ∈ supp t → ¬ (x = y) → x' # σ y) :
    σ * (x ． t) = (x' ． (σ ∘/ x ≔ (Trm.atom x' : Trm Sg 0)) * t) :=
  sbCls σ x x' _ t f rfl

/-- Agda: `rnAbs` (WSLN/Sig/Abstraction.agda). -/
theorem rnAbs {Sg : Sig} {m : Nat} (ρ : Rn) (x x' : Atom) (t : Trm Sg m)
    (f : ∀ y, y ∈ supp t → ¬ (x = y) → ¬ (x' = ρ y)) :
    ρ * (x ． t) = (x' ． ((ρ ∘/ x ≔ʳ x') : Rn) * t) := by
  show (Sb.ofRn ρ : Sb Sg) * (x ． t) = _
  rw [sbAbs (Sb.ofRn ρ) x x' t fun y hy hne => .single (f y hy hne)]
  exact congrArg (Trm.abs x') (updateRn ρ x x' t)

/-! ## Alpha equivalence -/

/-- Agda: `alphaEquiv` (WSLN/Sig/Abstraction.agda). -/
theorem alphaEquiv {Sg : Sig} {n : Nat} (x x' : Atom) (t : Trm Sg n) (h : x' # t) :
    (x ． t) = (x' ． ((x ≔ʳ x') : Rn) * t) :=
  calc (x ． t)
      = (x' ． (x ． t)[x']) := (absConc x' (x ． t) (fresh_abs' t h)).symm
    _ = (x' ． ((x ≔ʳ x') : Rn) * t) := by
        refine congrArg (Trm.abs x') ?_
        rw [conc_atom, ← conc_trm, concAbs x t (Trm.atom x')]
        exact updateRn Rn.id x x' t

end WSLN

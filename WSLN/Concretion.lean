import WSLN.Substitution

/-!
# Opening and concretion

Port of `agda-code/agda/WSLN/Sig/Concretion.agda`.

`opn`/`opnArg` are defined with Agda's "equation trick": the scope equation
`m = n + 1` is an explicit argument rather than a pattern, because the recursive
call under a binder of depth `k` needs `k + m = (k + n) + 1`.  Indices are aligned
with `Fin.cast` before `remove`.

Agda's `ConcretionSyntax` record becomes two `GetElem` instances, so `t [ u ]`,
`t [ x ]` and the iterated forms `t [ u ] [ v ]` read as in the Agda source.
-/

namespace WSLN

/-! ## Opening -/

mutual

/-- Agda: `opn` (WSLN/Sig/Concretion.agda). -/
def opn {Sg : Sig} {m n : Nat} (i : Fin m) (u : Trm Sg 0) (t : Trm Sg m)
    (e : m = n + 1) : Trm Sg n :=
  match t with
  | .var j =>
      if h : i = j then
        -- the inclusion of `Trm Sg 0` into `Trm Sg n`
        u.weaken n (Nat.zero_le n)
      else
        -- removing an index while maintaining the order of the others
        .var (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h))
  | .atom x => .atom x
  | .op o ts => .op o (opnArg i u ts e)

/-- Agda: `opn'` (WSLN/Sig/Concretion.agda). -/
def opnArg {Sg : Sig} {m n : Nat} {ms : List Nat} (i : Fin m) (u : Trm Sg 0)
    (ts : Arg Sg m ms) (e : m = n + 1) : Arg Sg n ms :=
  match ts with
  | .nil => .nil
  | .cons (m := k) t us =>
      .cons (opn (shiftIdx k i) u t (by omega)) (opnArg i u us e)

end

theorem opn_var {Sg : Sig} {m n : Nat} (i : Fin m) (u : Trm Sg 0) (j : Fin m)
    (e : m = n + 1) :
    opn i u (.var j) e
      = if h : i = j then u.weaken n (Nat.zero_le n)
        else .var (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h)) := rfl

@[simp] theorem opn_var_eq {Sg : Sig} {m n : Nat} (i : Fin m) (u : Trm Sg 0)
    (e : m = n + 1) : opn i u (.var i) e = u.weaken n (Nat.zero_le n) := by
  rw [opn_var]; simp

theorem opn_var_val_eq {Sg : Sig} {m n : Nat} {i j : Fin m} (u : Trm Sg 0)
    (e : m = n + 1) (h : i.val = j.val) :
    opn i u (.var j) e = u.weaken n (Nat.zero_le n) := by
  rw [opn_var, dif_pos (Fin.ext h)]

theorem opn_var_ne {Sg : Sig} {m n : Nat} {i j : Fin m} (u : Trm Sg 0) (e : m = n + 1)
    (h : i ≠ j) :
    opn i u (.var j) e = .var (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h)) := by
  rw [opn_var]; simp [h]

@[simp] theorem opn_atom {Sg : Sig} {m n : Nat} (i : Fin m) (u : Trm Sg 0) (x : Atom)
    (e : m = n + 1) : opn i u (.atom x) e = .atom x := rfl

@[simp] theorem opn_op {Sg : Sig} {m n : Nat} (i : Fin m) (u : Trm Sg 0) (o : Sg.Op)
    (ts : Arg Sg m (Sg.ar o)) (e : m = n + 1) :
    opn i u (.op o ts) e = .op o (opnArg i u ts e) := rfl

@[simp] theorem opnArg_nil {Sg : Sig} {m n : Nat} (i : Fin m) (u : Trm Sg 0)
    (e : m = n + 1) : opnArg i u (Arg.nil : Arg Sg m []) e = .nil := rfl

@[simp] theorem opnArg_cons {Sg : Sig} {m n k : Nat} {ms : List Nat} (i : Fin m)
    (u : Trm Sg 0) (t : Trm Sg (m + k)) (us : Arg Sg m ms) (e : m = n + 1) :
    opnArg i u (Arg.cons t us) e
      = .cons (opn (shiftIdx k i) u t (by omega)) (opnArg i u us e) := rfl

/-- Agda: `_~>_` (WSLN/Sig/Concretion.agda). -/
def Trm.openAt {Sg : Sig} {n : Nat} (i : Fin (n + 1)) (u : Trm Sg 0)
    (t : Trm Sg (n + 1)) : Trm Sg n := opn i u t rfl

/-- Agda: `_~>'_` (WSLN/Sig/Concretion.agda). -/
def Arg.openAt {Sg : Sig} {n : Nat} {ms : List Nat} (i : Fin (n + 1)) (u : Trm Sg 0)
    (ts : Arg Sg (n + 1) ms) : Arg Sg n ms := opnArg i u ts rfl

/-! ## Concretion -/

/-- Agda: `_[_]` (WSLN/Sig/Concretion.agda), the `i = zero` case of opening. -/
def Trm.conc {Sg : Sig} {n : Nat} (t : Trm Sg (n + 1)) (u : Trm Sg 0) : Trm Sg n :=
  opn ⟨0, Nat.succ_pos n⟩ u t rfl

/-- Agda: `ConcretionSyntaxTrm` (WSLN/Sig/Concretion.agda). -/
instance instGetElemTrmTrm {Sg : Sig} {n : Nat} :
    GetElem (Trm Sg (n + 1)) (Trm Sg 0) (Trm Sg n) (fun _ _ => True) where
  getElem t u _ := t.conc u

/-- Agda: `ConcretionSyntax𝔸` (WSLN/Sig/Concretion.agda).  Lets one write
`t [ x ]` for `t [ 𝐚 x ]`. -/
instance instGetElemTrmAtom {Sg : Sig} {n : Nat} :
    GetElem (Trm Sg (n + 1)) Atom (Trm Sg n) (fun _ _ => True) where
  getElem t x _ := t.conc (.atom x)

@[simp] theorem conc_trm {Sg : Sig} {n : Nat} (t : Trm Sg (n + 1)) (u : Trm Sg 0) :
    t[u] = t.conc u := rfl

@[simp] theorem conc_atom {Sg : Sig} {n : Nat} (t : Trm Sg (n + 1)) (x : Atom) :
    t[x] = t.conc (.atom x) := rfl

/-- Concretion of the outermost index: `i0 [ u ] = u.weaken n`. -/
@[simp] theorem conc_var_zero {Sg : Sig} {n : Nat} {j : Fin (n + 1)} (u : Trm Sg 0)
    (h : j.val = 0) :
    (Trm.var j : Trm Sg (n + 1)).conc u = u.weaken n (Nat.zero_le n) :=
  opn_var_val_eq u rfl h.symm

/-- Concretion of an inner index shifts it down by one. -/
@[simp] theorem conc_var_ne {Sg : Sig} {n : Nat} {j : Fin (n + 1)} (u : Trm Sg 0)
    (h : j.val ≠ 0) :
    (Trm.var j : Trm Sg (n + 1)).conc u = .var ⟨j.val - 1, by have := j.isLt; omega⟩ := by
  have hne : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) ≠ j := fun e => h (congrArg Fin.val e).symm
  rw [Trm.conc, opn_var_ne u rfl hne]
  refine congrArg Trm.var (Fin.ext ?_)
  simp only [remove_val, Fin.val_cast]
  rw [if_neg (by omega : ¬ (j.val < 0))]

/-! ## Finite support properties of opening and concretion -/

mutual

/-- Agda: `opnSupp` (WSLN/Sig/Concretion.agda). -/
theorem opnSupp {Sg : Sig} {m n : Nat} (i : Fin m) (u : Trm Sg 0) (t : Trm Sg m)
    (e : m = n + 1) : supp t ⊆ supp (opn i u t e) := by
  match t with
  | .var j => intro x hx; cases hx
  | .atom x => intro y hy; simpa using hy
  | .op o ts => intro x hx; exact opnSuppArg i u ts e hx

/-- Agda: `opnSupp'` (WSLN/Sig/Concretion.agda). -/
theorem opnSuppArg {Sg : Sig} {m n : Nat} {ms : List Nat} (i : Fin m) (u : Trm Sg 0)
    (ts : Arg Sg m ms) (e : m = n + 1) : supp ts ⊆ supp (opnArg i u ts e) := by
  match ts with
  | .nil => intro x hx; cases hx
  | .cons (m := k) t us =>
      intro x hx
      simp only [opnArg_cons, supp_cons]
      cases hx with
      | unionL p => exact .unionL (opnSupp (shiftIdx k i) u t (by omega) p)
      | unionR p => exact .unionR (opnSuppArg i u us e p)

end

/-- Agda: `[]supp` (WSLN/Sig/Concretion.agda). -/
theorem conc_supp {Sg : Sig} {n : Nat} (t : Trm Sg (n + 1)) (u : Trm Sg 0) :
    supp t ⊆ supp (t[u]) := opnSupp _ u t rfl

/-- Agda: `[]²supp` (WSLN/Sig/Concretion.agda). -/
theorem conc_supp₂ {Sg : Sig} {n : Nat} (t : Trm Sg (n + 2)) (u v : Trm Sg 0) :
    supp t ⊆ supp (t[u][v]) :=
  Fset.subset_trans (conc_supp t u) (conc_supp (t[u]) v)

mutual

/-- Agda: `suppOpn` (WSLN/Sig/Concretion.agda). -/
theorem suppOpn {Sg : Sig} {m n : Nat} (i : Fin m) (u : Trm Sg 0) (t : Trm Sg m)
    (e : m = n + 1) : supp (opn i u t e) ⊆ supp t ∪ supp u := by
  match t with
  | .var j =>
      intro x hx
      by_cases h : i = j
      · subst h
        rw [opn_var_eq, Trm.supp_weaken] at hx
        exact .unionR hx
      · rw [opn_var_ne u e h] at hx
        cases hx
  | .atom y => intro x hx; exact .unionL hx
  | .op o ts => intro x hx; exact suppOpnArg i u ts e hx

/-- Agda: `suppOpn'` (WSLN/Sig/Concretion.agda). -/
theorem suppOpnArg {Sg : Sig} {m n : Nat} {ms : List Nat} (i : Fin m) (u : Trm Sg 0)
    (ts : Arg Sg m ms) (e : m = n + 1) : supp (opnArg i u ts e) ⊆ supp ts ∪ supp u := by
  match ts with
  | .nil => intro x hx; cases hx
  | .cons (m := k) t us =>
      intro x hx
      simp only [opnArg_cons, supp_cons] at hx
      cases hx with
      | unionL p =>
          cases suppOpn (shiftIdx k i) u t (by omega) p with
          | unionL q => exact .unionL (.unionL q)
          | unionR q => exact .unionR q
      | unionR p =>
          cases suppOpnArg i u us e p with
          | unionL q => exact .unionL (.unionR q)
          | unionR q => exact .unionR q

end

/-- Agda: `supp[]` (WSLN/Sig/Concretion.agda). -/
theorem supp_conc {Sg : Sig} {n : Nat} (t : Trm Sg (n + 1)) (u : Trm Sg 0) :
    supp (t[u]) ⊆ supp t ∪ supp u := suppOpn _ u t rfl

/-- Agda: `supp[]²` (WSLN/Sig/Concretion.agda). -/
theorem supp_conc₂ {Sg : Sig} {n : Nat} (t : Trm Sg (n + 2)) (u v : Trm Sg 0) :
    supp (t[u][v]) ⊆ (supp t ∪ supp u) ∪ supp v :=
  Fset.subset_trans (supp_conc (t[u]) v)
    (Fset.union_subset_union (supp_conc t u) Fset.subset_refl)

/-! ## Opening at an index greater than those in the term -/

/-- Agda: `opnFin<` (WSLN/Sig/Concretion.agda). -/
theorem opnFin_lt {m n : Nat} (i : Fin m) (j : Fin n) (q : m ≤ j.val) (h : m ≤ n) :
    Fin.castLE h i ≠ j := by
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_castLE] at hv
  have := i.isLt
  omega

mutual

/-- Agda: `opn<` (WSLN/Sig/Concretion.agda). -/
theorem opn_lt {Sg : Sig} {k m n : Nat} (i : Fin n) (u : Trm Sg 0) (e : n = m + 1)
    (q : k ≤ i.val) (h₁ : k ≤ m) (h₂ : k ≤ n) (t : Trm Sg k) :
    opn i u (t.weaken n h₂) e = t.weaken m h₁ := by
  match t with
  | .var j =>
      have hj := j.isLt
      have hne : i ≠ Fin.castLE h₂ j := by
        intro he
        have hv := congrArg (fun (l : Fin n) => l.val) he
        simp only [Fin.val_castLE] at hv
        omega
      rw [Trm.weaken_var, opn_var_ne u e hne, Trm.weaken_var]
      refine congrArg Trm.var (Fin.ext ?_)
      simp only [remove_val, Fin.val_cast, Fin.val_castLE]
      rw [if_pos (by omega : j.val < i.val)]
  | .atom x => simp
  | .op o ts => simpa using opnArg_lt i u e q h₁ h₂ ts

/-- Agda: `opn<'` (WSLN/Sig/Concretion.agda). -/
theorem opnArg_lt {Sg : Sig} {k m n : Nat} {ms : List Nat} (i : Fin n) (u : Trm Sg 0)
    (e : n = m + 1) (q : k ≤ i.val) (h₁ : k ≤ m) (h₂ : k ≤ n) (ts : Arg Sg k ms) :
    opnArg i u (ts.weaken n h₂) e = ts.weaken m h₁ := by
  match ts with
  | .nil => simp
  | .cons (m := j) t us =>
      simp only [Arg.weaken_cons, opnArg_cons, Arg.cons.injEq]
      refine ⟨?_, opnArg_lt i u e q h₁ h₂ us⟩
      exact opn_lt (shiftIdx j i) u (by omega) (by simp only [val_shiftIdx]; omega)
        (by omega) (by omega) t

end

/-- Concretion of a locally closed term's weakening drops one scope level. -/
@[simp] theorem conc_weaken_zero {Sg : Sig} {n : Nat} (t : Trm Sg 0) (v : Trm Sg 0) :
    (t.weaken (n + 1) (Nat.zero_le _)).conc v = t.weaken n (Nat.zero_le n) :=
  opn_lt _ v rfl (Nat.zero_le _) (Nat.zero_le n) (Nat.zero_le (n + 1)) t

/-! ## Substitution and renaming commute with opening and concretion -/

mutual

/-- Agda: `sbOpn` (WSLN/Sig/Concretion.agda). -/
theorem sbOpn {Sg : Sig} {m n : Nat} (σ : Sb Sg) (i : Fin m) (u : Trm Sg 0)
    (t : Trm Sg m) (e : m = n + 1) :
    σ * (opn i u t e) = opn i (σ * u) (σ * t) e := by
  match t with
  | .var j =>
      by_cases h : i = j
      · subst h
        rw [actSb_var, opn_var_eq, opn_var_eq]
        exact sbWeaken u n (Nat.zero_le n) σ
      · rw [actSb_var, opn_var_ne u e h, opn_var_ne (σ * u) e h, actSb_var]
  | .atom x =>
      rw [opn_atom, actSb_atom, actSb_atom]
      exact (opn_lt i (σ * u) e (Nat.zero_le _) (Nat.zero_le n) (Nat.zero_le m) (σ x)).symm
  | .op o ts => simpa using sbOpnArg σ i u ts e

/-- Agda: `sbOpn'` (WSLN/Sig/Concretion.agda). -/
theorem sbOpnArg {Sg : Sig} {m n : Nat} {ms : List Nat} (σ : Sb Sg) (i : Fin m)
    (u : Trm Sg 0) (ts : Arg Sg m ms) (e : m = n + 1) :
    σ * (opnArg i u ts e) = opnArg i (σ * u) (σ * ts) e := by
  match ts with
  | .nil => rfl
  | .cons (m := k) t us =>
      simp only [opnArg_cons, actSb_cons, Arg.cons.injEq]
      exact ⟨sbOpn σ (shiftIdx k i) u t (by omega), sbOpnArg σ i u us e⟩

end

/-- Agda: `sb[]` (WSLN/Sig/Concretion.agda). -/
theorem sb_conc {Sg : Sig} {n : Nat} (σ : Sb Sg) (t : Trm Sg (n + 1)) (u : Trm Sg 0) :
    σ * (t[u]) = (σ * t)[σ * u] := sbOpn σ _ u t rfl

/-- Agda: `rn[]` (WSLN/Sig/Concretion.agda). -/
theorem rn_conc {Sg : Sig} {n : Nat} (ρ : Rn) (t : Trm Sg (n + 1)) (u : Trm Sg 0) :
    ρ * (t[u]) = (ρ * t)[ρ * u] := sb_conc (Sb.ofRn ρ) t u

/-- Agda: `sb[]²` (WSLN/Sig/Concretion.agda). -/
theorem sb_conc₂ {Sg : Sig} {n : Nat} (σ : Sb Sg) (t : Trm Sg (n + 2)) (u u' : Trm Sg 0) :
    σ * (t[u][u']) = (σ * t)[σ * u][σ * u'] := by
  rw [sb_conc σ (t[u]) u', sb_conc σ t u]

/-- Agda: `rn[]²` (WSLN/Sig/Concretion.agda). -/
theorem rn_conc₂ {Sg : Sig} {n : Nat} (ρ : Rn) (t : Trm Sg (n + 2)) (u u' : Trm Sg 0) :
    ρ * (t[u][u']) = (ρ * t)[ρ * u][ρ * u'] := sb_conc₂ (Sb.ofRn ρ) t u u'

/-! ## Concretion at an updated substitution -/

/-- Agda: `sbUpdate[]` (WSLN/Sig/Concretion.agda). -/
theorem sbUpdate_conc {Sg : Sig} {n : Nat} (σ : Sb Sg) (x : Atom) (u : Trm Sg 0)
    (t : Trm Sg (n + 1)) (h : x # t) : (σ ∘/ x ≔ u) * (t[x]) = (σ * t)[u] := by
  rw [conc_atom, ← conc_trm, sb_conc (σ ∘/ x ≔ u) t (Trm.atom x),
    updateFresh σ x u t h, updateEq σ u x]

/-- Agda: `sbUpdate[]²` (WSLN/Sig/Concretion.agda). -/
theorem sbUpdate_conc₂ {Sg : Sig} {n : Nat} (σ : Sb Sg) (x y : Atom) (u v : Trm Sg 0)
    (t : Trm Sg (n + 2)) (hx : x # t) (hy : y # (t, x)) :
    ((σ ∘/ x ≔ u) ∘/ y ≔ v) * (t[x][y]) = (σ * t)[u][v] := by
  have hyt : y # t := Fset.notMem_union_left hy
  have hyx : y ≠ x := Fset.ne_of_notMem_single (Fset.notMem_union_right hy)
  rw [conc_atom, conc_atom, ← conc_trm, ← conc_trm,
    sb_conc₂ ((σ ∘/ x ≔ u) ∘/ y ≔ v) t (Trm.atom x) (Trm.atom y),
    updateFresh (σ ∘/ x ≔ u) y v t hyt, updateFresh σ x u t hx]
  have e₁ : ((σ ∘/ x ≔ u) ∘/ y ≔ v) * (Trm.atom x : Trm Sg 0) = u := by
    rw [actSb_atom, Sb.update_neq _ _ hyx, Sb.update_eq]
    simp
  have e₂ : ((σ ∘/ x ≔ u) ∘/ y ≔ v) * (Trm.atom y : Trm Sg 0) = v := updateEq _ v y
  rw [e₁, e₂]

/-- Agda: `rnUpdate[]` (WSLN/Sig/Concretion.agda). -/
theorem rnUpdate_conc {Sg : Sig} {n : Nat} (ρ : Rn) (x x' : Atom) (t : Trm Sg (n + 1))
    (h : x # t) : ((ρ ∘/ x ≔ʳ x') : Rn) * (t[x]) = (ρ * t)[x'] := by
  show (Sb.ofRn (ρ ∘/ x ≔ʳ x') : Sb Sg) * (t[x]) = ((Sb.ofRn ρ : Sb Sg) * t)[x']
  rw [← updateRn (Sg := Sg) ρ x x' (t[x])]
  exact sbUpdate_conc (Sb.ofRn ρ) x (Trm.atom x') t h

/-- Agda: `rnUpdate[]²` (WSLN/Sig/Concretion.agda). -/
theorem rnUpdate_conc₂ {Sg : Sig} {n : Nat} (ρ : Rn) (x x' y y' : Atom)
    (t : Trm Sg (n + 2)) (hx : x # t) (hy : y # (t, x)) :
    (((ρ ∘/ x ≔ʳ x') ∘/ y ≔ʳ y') : Rn) * (t[x][y]) = (ρ * t)[x'][y'] := by
  show (Sb.ofRn ((ρ ∘/ x ≔ʳ x') ∘/ y ≔ʳ y') : Sb Sg) * (t[x][y])
    = ((Sb.ofRn ρ : Sb Sg) * t)[x'][y']
  rw [← updateRn₂ (Sg := Sg) ρ x x' y y' (t[x][y])]
  exact sbUpdate_conc₂ (Sb.ofRn ρ) x y (Trm.atom x') (Trm.atom y') t hx hy

/-- Agda: `ssb[]` (WSLN/Sig/Concretion.agda). -/
theorem ssb_conc {Sg : Sig} {n : Nat} (x : Atom) (u : Trm Sg 0) (t : Trm Sg (n + 1))
    (h : x # t) : (x ≔ u) * (t[x]) = t[u] := by
  rw [show (x ≔ u) = ((Sb.id : Sb Sg) ∘/ x ≔ u) from rfl,
    sbUpdate_conc Sb.id x u t h, sbUnit]

/-- Agda: `ssb[]²` (WSLN/Sig/Concretion.agda). -/
theorem ssb_conc₂ {Sg : Sig} {n : Nat} (x y : Atom) (u v : Trm Sg 0) (t : Trm Sg (n + 2))
    (hx : x # t) (hy : y # (t, x)) : ((x ≔ u) ∘/ y ≔ v) * (t[x][y]) = t[u][v] := by
  rw [show (x ≔ u) = ((Sb.id : Sb Sg) ∘/ x ≔ u) from rfl,
    sbUpdate_conc₂ Sb.id x y u v t hx hy, sbUnit]

/-- Agda: `srn[]` (WSLN/Sig/Concretion.agda). -/
theorem srn_conc {Sg : Sig} {n : Nat} (x x' : Atom) (t : Trm Sg (n + 1)) (h : x # t) :
    ((x ≔ʳ x') : Rn) * (t[x]) = t[x'] := by
  rw [show ((x ≔ʳ x') : Rn) = (Rn.id ∘/ x ≔ʳ x') from rfl,
    rnUpdate_conc (Sg := Sg) Rn.id x x' t h, rnUnit]

/-- Agda: `srn[]²` (WSLN/Sig/Concretion.agda). -/
theorem srn_conc₂ {Sg : Sig} {n : Nat} (x x' y y' : Atom) (t : Trm Sg (n + 2))
    (hx : x # t) (hy : y # (t, x)) :
    (((x ≔ʳ x') ∘/ y ≔ʳ y') : Rn) * (t[x][y]) = t[x'][y'] := by
  rw [show ((x ≔ʳ x') : Rn) = (Rn.id ∘/ x ≔ʳ x') from rfl,
    rnUpdate_conc₂ (Sg := Sg) Rn.id x x' y y' t hx hy, rnUnit]

end WSLN

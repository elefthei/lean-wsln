import WSLN.Abstraction

/-!
# Size of terms

Port of `agda-code/agda/WSLN/Sig/Size.agda`.

`Trm Sg 0` is not inductively generated on its own, so functions on locally closed
terms are often defined by recursion on this notion of size, which is preserved by
abstraction, by concretion with a name, and by renaming.
-/

namespace WSLN

mutual

def Trm.size {Sg : Sig} {n : Nat} : Trm Sg n → Nat
  | .var _ => 0
  | .atom _ => 0
  | .op _ ts => Arg.size ts + 1

def Arg.size {Sg : Sig} {n : Nat} {ms : List Nat} : Arg Sg n ms → Nat
  | .nil => 0
  | .cons t ts => max (Trm.size t) (Arg.size ts)

end

@[simp] theorem Trm.size_var {Sg : Sig} {n : Nat} (i : Fin n) :
    (Trm.var i : Trm Sg n).size = 0 := rfl

@[simp] theorem Trm.size_atom {Sg : Sig} {n : Nat} (x : Atom) :
    (Trm.atom x : Trm Sg n).size = 0 := rfl

@[simp] theorem Trm.size_op {Sg : Sig} {n : Nat} (o : Sg.Op) (ts : Arg Sg n (Sg.ar o)) :
    (Trm.op o ts).size = ts.size + 1 := rfl

@[simp] theorem Arg.size_nil {Sg : Sig} {n : Nat} :
    (Arg.nil : Arg Sg n []).size = 0 := rfl

@[simp] theorem Arg.size_cons {Sg : Sig} {n k : Nat} {ms : List Nat} (t : Trm Sg (n + k))
    (ts : Arg Sg n ms) : (Arg.cons t ts).size = max t.size ts.size := rfl

/-! ## Scope extension preserves size -/

mutual

@[simp] theorem Trm.size_weaken {Sg : Sig} {m n : Nat} (t : Trm Sg m) (h : m ≤ n) :
    (t.weaken n h).size = t.size := by
  match t with
  | .var i => rfl
  | .atom x => rfl
  | .op o ts => simpa using Arg.size_weaken ts h

@[simp] theorem Arg.size_weaken {Sg : Sig} {m n : Nat} {ms : List Nat}
    (ts : Arg Sg m ms) (h : m ≤ n) : (ts.weaken n h).size = ts.size := by
  match ts with
  | .nil => rfl
  | .cons (m := k) t us =>
      simp only [Arg.weaken_cons, Arg.size_cons]
      rw [Trm.size_weaken t (by omega : m + k ≤ n + k), Arg.size_weaken us h]

end

/-! ## Concreting an index with a name preserves size -/

mutual

theorem sizeOpn {Sg : Sig} {m n : Nat} (i : Fin m) (x : Atom) (t : Trm Sg m)
    (e : m = n + 1) : (opn i (Trm.atom x) t e).size = t.size := by
  match t with
  | .var j =>
      by_cases h : i = j
      · subst h; rw [opn_var_eq]; simp
      · rw [opn_var_ne (Trm.atom x) e h]; simp
  | .atom y => simp
  | .op o ts => simpa using sizeOpnArg i x ts e

theorem sizeOpnArg {Sg : Sig} {m n : Nat} {ms : List Nat} (i : Fin m) (x : Atom)
    (ts : Arg Sg m ms) (e : m = n + 1) : (opnArg i (Trm.atom x) ts e).size = ts.size := by
  match ts with
  | .nil => rfl
  | .cons (m := k) t us =>
      simp only [opnArg_cons, Arg.size_cons]
      rw [sizeOpn (shiftIdx k i) x t (by omega), sizeOpnArg i x us e]

end

@[simp] theorem size_conc {Sg : Sig} {n : Nat} (t : Trm Sg (n + 1)) (x : Atom) :
    (t[x]).size = t.size := sizeOpn _ x t rfl

theorem size_conc_le {Sg : Sig} {s n : Nat} (t : Trm Sg (n + 1)) (x : Atom)
    (h : t.size ≤ s) : (t[x]).size ≤ s := by rw [size_conc]; exact h

/-! ## Abstracting a name preserves size -/

mutual

theorem sizeCls {Sg : Sig} {m n : Nat} (x : Atom) (i : Fin n) (t : Trm Sg m)
    (e : n = m + 1) : (cls x i t e).size = t.size := by
  match t with
  | .var j => simp
  | .atom y =>
      by_cases h : x = y
      · subst h; rw [cls_atom_eq]; simp
      · rw [cls_atom_ne i e h]; simp
  | .op o ts => simpa using sizeClsArg x i ts e

theorem sizeClsArg {Sg : Sig} {m n : Nat} {ms : List Nat} (x : Atom) (i : Fin n)
    (ts : Arg Sg m ms) (e : n = m + 1) : (clsArg x i ts e).size = ts.size := by
  match ts with
  | .nil => rfl
  | .cons (m := k) t us =>
      simp only [clsArg_cons, Arg.size_cons]
      rw [sizeCls x (shiftIdx k i) t (by omega), sizeClsArg x i us e]

end

@[simp] theorem size_abs {Sg : Sig} {n : Nat} (x : Atom) (t : Trm Sg n) :
    (x ． t).size = t.size := sizeCls x _ t rfl

theorem size_abs_le {Sg : Sig} {s n : Nat} (x : Atom) (t : Trm Sg n) (h : t.size ≤ s) :
    (x ． t).size ≤ s := by rw [size_abs]; exact h

/-! ## Renaming preserves size -/

mutual

@[simp] theorem Trm.size_rn {Sg : Sig} {n : Nat} (t : Trm Sg n) (ρ : Rn) :
    (ρ * t).size = t.size := by
  match t with
  | .var i => rfl
  | .atom x => simp [Sb.ofRn]
  | .op o ts => simpa using Arg.size_rn ts ρ

@[simp] theorem Arg.size_rn {Sg : Sig} {n : Nat} {ms : List Nat} (ts : Arg Sg n ms)
    (ρ : Rn) : (ρ * ts).size = ts.size := by
  match ts with
  | .nil => rfl
  | .cons t us =>
      simp only [actRn_arg, actSb_cons, Arg.size_cons]
      rw [← actRn_trm ρ t, ← actRn_arg ρ us, Trm.size_rn t ρ, Arg.size_rn us ρ]

end

end WSLN

import WSLN.Sig

/-!
# Terms over a binding signature

Port of `agda-code/agda/WSLN/Sig/Term.agda`.

`Trm Sg n` are the terms over `Sg` in scope `n`, `Arg Sg n ms` their argument lists.
Agda's `isSet`/`hedberg` machinery, needed there to compare the transported argument
lists in `decTrmEq`, is dropped: Lean's equality proofs are irrelevant.
-/

namespace WSLN

/-! ## The scoped set of terms -/

mutual

/-- Terms over `Sg` in scope `n`. -/
inductive Trm (Sg : Sig) : Nat → Type where
  /-- A well-scoped de Bruijn index. -/
  | var {n : Nat} (i : Fin n) : Trm Sg n
  /-- An atomic name. -/
  | atom {n : Nat} (x : Atom) : Trm Sg n
  /-- A compound term. -/
  | op {n : Nat} (o : Sg.Op) (ts : Arg Sg n (Sg.ar o)) : Trm Sg n

/-- The arguments of a term constructor. -/
inductive Arg (Sg : Sig) : Nat → List Nat → Type where
  | nil {n : Nat} : Arg Sg n []
  | cons {n m : Nat} {ms : List Nat} (t : Trm Sg (n + m)) (ts : Arg Sg n ms) :
      Arg Sg n (m :: ms)

end

/-- The locally closed terms. -/
abbrev Trm0 (Sg : Sig) := Trm Sg 0

abbrev Arg0 (Sg : Sig) (ms : List Nat) := Arg Sg 0 ms

@[inherit_doc Trm.var] scoped notation:max "𝐢" i:max => WSLN.Trm.var i
@[inherit_doc Trm.atom] scoped notation:max "𝐚" x:max => WSLN.Trm.atom x
@[inherit_doc Trm.op] scoped notation:max "𝐨 " o:max ts:max => WSLN.Trm.op o ts

abbrev i0 {Sg : Sig} {n : Nat} : Trm Sg (n + 1) := .var ⟨0, by omega⟩
abbrev i1 {Sg : Sig} {n : Nat} : Trm Sg (n + 2) := .var ⟨1, by omega⟩
abbrev i2 {Sg : Sig} {n : Nat} : Trm Sg (n + 3) := .var ⟨2, by omega⟩

/-! ## Scope weakening -/

mutual

def Trm.weaken {Sg : Sig} {m : Nat} (t : Trm Sg m) (n : Nat) (h : m ≤ n := by omega) :
    Trm Sg n :=
  match t with
  | .var i => .var (Fin.castLE h i)
  | .atom x => .atom x
  | .op o ts => .op o (Arg.weaken ts n h)

def Arg.weaken {Sg : Sig} {m : Nat} {ms : List Nat} (ts : Arg Sg m ms) (n : Nat)
    (h : m ≤ n := by omega) : Arg Sg n ms :=
  match ts with
  | .nil => .nil
  | .cons (m := k) t us => .cons (Trm.weaken t (n + k) (by omega)) (Arg.weaken us n h)

end

/-! ### Defining equations of `weaken`

Lean-only, no Agda counterpart: Agda's clausal definitions reduce definitionally at
each constructor, so these `rfl` lemmas only restore that convenience to `simp`. -/

@[simp] theorem Trm.weaken_var {Sg : Sig} {m n : Nat} (i : Fin m) (h : m ≤ n) :
    (Trm.var i : Trm Sg m).weaken n h = .var (Fin.castLE h i) := rfl

@[simp] theorem Trm.weaken_atom {Sg : Sig} {m n : Nat} (x : Atom) (h : m ≤ n) :
    (Trm.atom x : Trm Sg m).weaken n h = .atom x := rfl

@[simp] theorem Trm.weaken_op {Sg : Sig} {m n : Nat} (o : Sg.Op) (ts : Arg Sg m (Sg.ar o))
    (h : m ≤ n) : (Trm.op o ts).weaken n h = .op o (ts.weaken n h) := rfl

@[simp] theorem Arg.weaken_nil {Sg : Sig} {m n : Nat} (h : m ≤ n) :
    (Arg.nil : Arg Sg m []).weaken n h = .nil := rfl

@[simp] theorem Arg.weaken_cons {Sg : Sig} {m n k : Nat} {ms : List Nat}
    (t : Trm Sg (m + k)) (ts : Arg Sg m ms) (h : m ≤ n) :
    (Arg.cons t ts).weaken n h
      = .cons (t.weaken (n + k) (by omega)) (ts.weaken n h) := rfl

mutual

@[simp] theorem Trm.weaken_self {Sg : Sig} {n : Nat} (t : Trm Sg n) (h : n ≤ n) :
    t.weaken n h = t := by
  match t with
  | .var i => simp
  | .atom x => simp
  | .op o ts => simp [Arg.weaken_self ts h]

@[simp] theorem Arg.weaken_self {Sg : Sig} {n : Nat} {ms : List Nat} (ts : Arg Sg n ms)
    (h : n ≤ n) : ts.weaken n h = ts := by
  match ts with
  | .nil => simp
  | .cons t us => simp [Trm.weaken_self t (by omega), Arg.weaken_self us h]

end

mutual

theorem Trm.weaken_trans {Sg : Sig} {k : Nat} (t : Trm Sg k) (m n : Nat)
    (h₁ : k ≤ m) (h₂ : m ≤ n) (h₃ : k ≤ n) :
    (t.weaken m h₁).weaken n h₂ = t.weaken n h₃ := by
  match t with
  | .var i => simp
  | .atom x => simp
  | .op o ts => simp [Arg.weaken_trans ts m n h₁ h₂ h₃]

theorem Arg.weaken_trans {Sg : Sig} {k : Nat} {ms : List Nat} (ts : Arg Sg k ms)
    (m n : Nat) (h₁ : k ≤ m) (h₂ : m ≤ n) (h₃ : k ≤ n) :
    (ts.weaken m h₁).weaken n h₂ = ts.weaken n h₃ := by
  match ts with
  | .nil => simp
  | .cons (m := j) t us =>
      simp [Trm.weaken_trans t (m + j) (n + j) (by omega) (by omega) (by omega),
        Arg.weaken_trans us m n h₁ h₂ h₃]

end

instance instScopedTrm {Sg : Sig} : Scoped (Trm Sg) where
  weaken t n h := t.weaken n h
  weaken_self t h := Trm.weaken_self t h
  weaken_trans t m n h₁ h₂ h₃ := Trm.weaken_trans t m n h₁ h₂ h₃

instance instScopedArg {Sg : Sig} {ms : List Nat} : Scoped (fun n => Arg Sg n ms) where
  weaken ts n h := ts.weaken n h
  weaken_self ts h := Arg.weaken_self ts h
  weaken_trans ts m n h₁ h₂ h₃ := Arg.weaken_trans ts m n h₁ h₂ h₃

@[simp] theorem weaken_trm {Sg : Sig} {m n : Nat} (t : Trm Sg m) (h : m ≤ n) :
    Scoped.weaken t n h = t.weaken n h := rfl

@[simp] theorem weaken_arg {Sg : Sig} {m n : Nat} {ms : List Nat} (ts : Arg Sg m ms)
    (h : m ≤ n) : Scoped.weaken (self := instScopedArg) ts n h = ts.weaken n h := rfl

/-! ## Constructor injectivity -/

/-- Injectivity of `𝐨`, specialised to a common operator; the general form is
`Trm.op.injEq`. -/
theorem Trm.op_inj {Sg : Sig} {n : Nat} {o : Sg.Op} {ts ts' : Arg Sg n (Sg.ar o)}
    (e : Trm.op o ts = Trm.op o ts') : ts = ts' := by
  rw [Trm.op.injEq] at e
  exact eq_of_heq e.2

/-- Injectivity of `𝐨`, operator component. -/
theorem Trm.op_inj_fst {Sg : Sig} {n : Nat} {o o' : Sg.Op} {ts : Arg Sg n (Sg.ar o)}
    {ts' : Arg Sg n (Sg.ar o')} (e : Trm.op o ts = Trm.op o' ts') : o = o' := by
  rw [Trm.op.injEq] at e
  exact e.1

theorem Arg.cons_inj {Sg : Sig} {n k : Nat} {ms : List Nat} {t t' : Trm Sg (n + k)}
    {ts ts' : Arg Sg n ms} (e : Arg.cons t ts = Arg.cons t' ts') : t = t' ∧ ts = ts' := by
  rw [Arg.cons.injEq] at e
  exact e

/-- Lean-only: congruence for `Trm.var` from equality of the index values. -/
theorem Trm.var_ext {Sg : Sig} {n : Nat} {i j : Fin n} (h : i.val = j.val) :
    (Trm.var i : Trm Sg n) = .var j := congrArg Trm.var (Fin.ext h)

/-! ## Decidable equality -/

mutual

def Trm.decEq {Sg : Sig} [DecidableEq Sg.Op] {n : Nat} :
    (t u : Trm Sg n) → Decidable (t = u)
  | .var i, .var j =>
      if h : i = j then isTrue (by subst h; rfl)
      else isFalse (by rw [Trm.var.injEq]; exact h)
  | .var _, .atom _ => isFalse nofun
  | .var _, .op _ _ => isFalse nofun
  | .atom _, .var _ => isFalse nofun
  | .atom x, .atom y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (by rw [Trm.atom.injEq]; exact h)
  | .atom _, .op _ _ => isFalse nofun
  | .op _ _, .var _ => isFalse nofun
  | .op _ _, .atom _ => isFalse nofun
  | .op o ts, .op o' ts' =>
      if h : o = o' then by
        subst h
        exact
          match Arg.decEq ts ts' with
          | isTrue e => isTrue (by subst e; rfl)
          | isFalse e => isFalse (fun he => e (Trm.op_inj he))
      else isFalse (fun he => h (Trm.op_inj_fst he))

def Arg.decEq {Sg : Sig} [DecidableEq Sg.Op] {n : Nat} {ms : List Nat} :
    (ts us : Arg Sg n ms) → Decidable (ts = us)
  | .nil, .nil => isTrue rfl
  | .cons t ts, .cons u us =>
      match Trm.decEq t u with
      | isFalse e => isFalse (fun he => e (Arg.cons_inj he).1)
      | isTrue e =>
          match Arg.decEq ts us with
          | isFalse e' => isFalse (fun he => e' (Arg.cons_inj he).2)
          | isTrue e' => isTrue (by subst e; subst e'; rfl)

end

instance instDecidableEqTrm {Sg : Sig} [DecidableEq Sg.Op] {n : Nat} :
    DecidableEq (Trm Sg n) := Trm.decEq

instance instDecidableEqArg {Sg : Sig} [DecidableEq Sg.Op] {n : Nat} {ms : List Nat} :
    DecidableEq (Arg Sg n ms) := Arg.decEq

/-! ## Finite support -/

mutual

def Trm.supp {Sg : Sig} {n : Nat} : Trm Sg n → Fset
  | .var _ => ∅
  | .atom x => ｛ x ｝
  | .op _ ts => Arg.supp ts

def Arg.supp {Sg : Sig} {n : Nat} {ms : List Nat} : Arg Sg n ms → Fset
  | .nil => ∅
  | .cons t ts => Trm.supp t ∪ Arg.supp ts

end

instance instFiniteSupportTrm {Sg : Sig} {n : Nat} : FiniteSupport (Trm Sg n) :=
  ⟨Trm.supp⟩

instance instFiniteSupportArg {Sg : Sig} {n : Nat} {ms : List Nat} :
    FiniteSupport (Arg Sg n ms) := ⟨Arg.supp⟩

@[simp] theorem supp_var {Sg : Sig} {n : Nat} (i : Fin n) :
    supp (Trm.var i : Trm Sg n) = ∅ := rfl

@[simp] theorem supp_atom {Sg : Sig} {n : Nat} (x : Atom) :
    supp (Trm.atom x : Trm Sg n) = ｛ x ｝ := rfl

@[simp] theorem supp_op {Sg : Sig} {n : Nat} (o : Sg.Op) (ts : Arg Sg n (Sg.ar o)) :
    supp (Trm.op o ts) = supp ts := rfl

@[simp] theorem supp_nil {Sg : Sig} {n : Nat} : supp (Arg.nil : Arg Sg n []) = ∅ := rfl

@[simp] theorem supp_cons {Sg : Sig} {n k : Nat} {ms : List Nat} (t : Trm Sg (n + k))
    (ts : Arg Sg n ms) : supp (Arg.cons t ts) = supp t ∪ supp ts := rfl

mutual

@[simp] theorem Trm.supp_weaken {Sg : Sig} {m : Nat} (t : Trm Sg m) (n : Nat)
    (h : m ≤ n) : supp (t.weaken n h) = supp t := by
  match t with
  | .var i => simp
  | .atom x => simp
  | .op o ts => simpa using Arg.supp_weaken ts n h

@[simp] theorem Arg.supp_weaken {Sg : Sig} {m : Nat} {ms : List Nat} (ts : Arg Sg m ms)
    (n : Nat) (h : m ≤ n) : supp (ts.weaken n h) = supp ts := by
  match ts with
  | .nil => simp
  | .cons (m := k) t us =>
      simp [Trm.supp_weaken t (n + k) (by omega), Arg.supp_weaken us n h]

end

end WSLN

import WSLN

/-!
# Nameful terms over a binding signature

Port of `agda-code/agda/Adequacy/Nameful.agda`.

The three mutually defined families of *nameful* (conventional, named-binder) syntax:
`NomTrm Sg` are terms, `NomArg Sg ms` argument lists, `NomBnd Sg m` a term under `m`
name binders.  Unicode constructor names are ASCII-ised (`𝐚` → `atom`, `𝐨` → `op`,
`[]`/`_::_` → `nil`/`cons`, `⟨⟩`/`⟨_,_⟩` → `base`/`abs`).

Agda's `hasSize` class has no counterpart in the Lean core port (`WSLN/Size.lean`
uses plain `Trm.size`/`Arg.size`), so `hasSizeNomTrm`/`hasSizeNomArg`/`hasSizeNomBnd`
become the dot-notation functions `NomTrm.size`/`NomArg.size`/`NomBnd.size`.

The `freshRen𝔸`/`freshRenTrm`/`freshRenArg`/`freshRenBnd` block of the Agda source is
commented out there and is not part of the module's API; it is not ported.
-/

namespace Adequacy

open WSLN

/-! ## Nameful terms -/

mutual

inductive NomTrm (Sg : Sig) : Type where
  /-- A name. -/
  | atom (x : Atom) : NomTrm Sg
  /-- A compound term. -/
  | op (o : Sg.Op) (bs : NomArg Sg (Sg.ar o)) : NomTrm Sg

inductive NomArg (Sg : Sig) : List Nat → Type where
  | nil : NomArg Sg []
  | cons {m : Nat} {ms : List Nat} (b : NomBnd Sg m) (bs : NomArg Sg ms) :
      NomArg Sg (m :: ms)

inductive NomBnd (Sg : Sig) : Nat → Type where
  /-- A term with no binders. -/
  | base (M : NomTrm Sg) : NomBnd Sg 0
  /-- Binding of one more name. -/
  | abs {m : Nat} (x : Atom) (b : NomBnd Sg m) : NomBnd Sg (m + 1)

end

/-! ## Freshness -/

mutual

def suppNomTrm {Sg : Sig} : NomTrm Sg → Fset
  | .atom x => ｛ x ｝
  | .op _ bs => suppNomArg bs

def suppNomArg {Sg : Sig} {ms : List Nat} : NomArg Sg ms → Fset
  | .nil => ∅
  | .cons b bs => suppNomBnd b ∪ suppNomArg bs

def suppNomBnd {Sg : Sig} {m : Nat} : NomBnd Sg m → Fset
  | .base M => suppNomTrm M
  | .abs x b => ｛ x ｝ ∪ suppNomBnd b

end

instance instFiniteSupportNomTrm {Sg : Sig} : FiniteSupport (NomTrm Sg) := ⟨suppNomTrm⟩

instance instFiniteSupportNomArg {Sg : Sig} {ms : List Nat} :
    FiniteSupport (NomArg Sg ms) := ⟨suppNomArg⟩

instance instFiniteSupportNomBnd {Sg : Sig} {m : Nat} :
    FiniteSupport (NomBnd Sg m) := ⟨suppNomBnd⟩

@[simp] theorem suppNom_atom {Sg : Sig} (x : Atom) :
    supp (NomTrm.atom x : NomTrm Sg) = ｛ x ｝ := rfl

@[simp] theorem suppNom_op {Sg : Sig} (o : Sg.Op) (bs : NomArg Sg (Sg.ar o)) :
    supp (NomTrm.op o bs) = supp bs := rfl

@[simp] theorem suppNomArg_nil {Sg : Sig} : supp (NomArg.nil : NomArg Sg []) = ∅ := rfl

@[simp] theorem suppNomArg_cons {Sg : Sig} {m : Nat} {ms : List Nat} (b : NomBnd Sg m)
    (bs : NomArg Sg ms) : supp (NomArg.cons b bs) = supp b ∪ supp bs := rfl

@[simp] theorem suppNomBnd_base {Sg : Sig} (M : NomTrm Sg) :
    supp (NomBnd.base M) = supp M := rfl

@[simp] theorem suppNomBnd_abs {Sg : Sig} {m : Nat} (x : Atom) (b : NomBnd Sg m) :
    supp (NomBnd.abs x b) = ｛ x ｝ ∪ supp b := rfl

/-! ## Renaming

All names are renamed, be they free, bound or binding. -/

mutual

def rnNomTrm {Sg : Sig} (ρ : Rn) : NomTrm Sg → NomTrm Sg
  | .atom x => .atom (ρ x)
  | .op o bs => .op o (rnNomArg ρ bs)

def rnNomArg {Sg : Sig} {ms : List Nat} (ρ : Rn) : NomArg Sg ms → NomArg Sg ms
  | .nil => .nil
  | .cons b bs => .cons (rnNomBnd ρ b) (rnNomArg ρ bs)

def rnNomBnd {Sg : Sig} {m : Nat} (ρ : Rn) : NomBnd Sg m → NomBnd Sg m
  | .base M => .base (rnNomTrm ρ M)
  | .abs x b => .abs (ρ x) (rnNomBnd ρ b)

end

instance instHMulRnNomTrm {Sg : Sig} : HMul Rn (NomTrm Sg) (NomTrm Sg) := ⟨rnNomTrm⟩

instance instHMulRnNomArg {Sg : Sig} {ms : List Nat} :
    HMul Rn (NomArg Sg ms) (NomArg Sg ms) := ⟨rnNomArg⟩

instance instHMulRnNomBnd {Sg : Sig} {m : Nat} :
    HMul Rn (NomBnd Sg m) (NomBnd Sg m) := ⟨rnNomBnd⟩

@[simp] theorem rnNom_atom {Sg : Sig} (ρ : Rn) (x : Atom) :
    ρ * (NomTrm.atom x : NomTrm Sg) = .atom (ρ x) := rfl

@[simp] theorem rnNom_op {Sg : Sig} (ρ : Rn) (o : Sg.Op) (bs : NomArg Sg (Sg.ar o)) :
    ρ * (NomTrm.op o bs) = .op o (ρ * bs) := rfl

@[simp] theorem rnNomArg_nil {Sg : Sig} (ρ : Rn) :
    ρ * (NomArg.nil : NomArg Sg []) = .nil := rfl

@[simp] theorem rnNomArg_cons {Sg : Sig} {m : Nat} {ms : List Nat} (ρ : Rn)
    (b : NomBnd Sg m) (bs : NomArg Sg ms) :
    ρ * (NomArg.cons b bs) = .cons (ρ * b) (ρ * bs) := rfl

@[simp] theorem rnNomBnd_base {Sg : Sig} (ρ : Rn) (M : NomTrm Sg) :
    ρ * (NomBnd.base M) = .base (ρ * M) := rfl

@[simp] theorem rnNomBnd_abs {Sg : Sig} {m : Nat} (ρ : Rn) (x : Atom) (b : NomBnd Sg m) :
    ρ * (NomBnd.abs x b) = .abs (ρ x) (ρ * b) := rfl

/-! ## Alpha equivalence -/

mutual

/-- α-equivalence of nameful terms. -/
inductive AlphaEq {Sg : Sig} : NomTrm Sg → NomTrm Sg → Prop where
  | atom (x : Atom) : AlphaEq (.atom x) (.atom x)
  | op {o : Sg.Op} {bs bs' : NomArg Sg (Sg.ar o)} (q : AlphaEqArg bs bs') :
      AlphaEq (.op o bs) (.op o bs')

/-- α-equivalence of nameful argument lists. -/
inductive AlphaEqArg {Sg : Sig} : {ms : List Nat} → NomArg Sg ms → NomArg Sg ms → Prop where
  | nil : AlphaEqArg (.nil : NomArg Sg []) .nil
  | cons {m : Nat} {ms : List Nat} {b b' : NomBnd Sg m} {bs bs' : NomArg Sg ms}
      (q₀ : AlphaEqBnd b b') (q₁ : AlphaEqArg bs bs') :
      AlphaEqArg (.cons b bs) (.cons b' bs')

/-- α-equivalence of nameful binders. -/
inductive AlphaEqBnd {Sg : Sig} : {m : Nat} → NomBnd Sg m → NomBnd Sg m → Prop where
  | base {M M' : NomTrm Sg} (q : AlphaEq M M') : AlphaEqBnd (.base M) (.base M')
  | abs {m : Nat} {x x' y : Atom} {b b' : NomBnd Sg m}
      (q₀ : AlphaEqBnd (((x ≔ʳ y) : Rn) * b) (((x' ≔ʳ y) : Rn) * b'))
      (q₁ : y # (b, b')) : AlphaEqBnd (.abs x b) (.abs x' b')

end

@[inherit_doc AlphaEq] scoped infix:4 " ~ " => Adequacy.AlphaEq
@[inherit_doc AlphaEqArg] scoped infix:4 " ~ᵃ " => Adequacy.AlphaEqArg
@[inherit_doc AlphaEqBnd] scoped infix:4 " ~ᵇ " => Adequacy.AlphaEqBnd

/-! ## Size -/

mutual

def NomTrm.size {Sg : Sig} : NomTrm Sg → Nat
  | .atom _ => 0
  | .op _ bs => NomArg.size bs + 1

def NomArg.size {Sg : Sig} {ms : List Nat} : NomArg Sg ms → Nat
  | .nil => 0
  | .cons b bs => max (NomBnd.size b) (NomArg.size bs)

def NomBnd.size {Sg : Sig} {m : Nat} : NomBnd Sg m → Nat
  | .base M => NomTrm.size M
  | .abs _ b => NomBnd.size b

end

@[simp] theorem NomTrm.size_atom {Sg : Sig} (x : Atom) :
    (NomTrm.atom x : NomTrm Sg).size = 0 := rfl

@[simp] theorem NomTrm.size_op {Sg : Sig} (o : Sg.Op) (bs : NomArg Sg (Sg.ar o)) :
    (NomTrm.op o bs).size = bs.size + 1 := rfl

@[simp] theorem NomArg.size_nil {Sg : Sig} : (NomArg.nil : NomArg Sg []).size = 0 := rfl

@[simp] theorem NomArg.size_cons {Sg : Sig} {m : Nat} {ms : List Nat} (b : NomBnd Sg m)
    (bs : NomArg Sg ms) : (NomArg.cons b bs).size = max b.size bs.size := rfl

@[simp] theorem NomBnd.size_base {Sg : Sig} (M : NomTrm Sg) :
    (NomBnd.base M).size = M.size := rfl

@[simp] theorem NomBnd.size_abs {Sg : Sig} {m : Nat} (x : Atom) (b : NomBnd Sg m) :
    (NomBnd.abs x b).size = b.size := rfl

/-! ## Renaming preserves size -/

mutual

@[simp] theorem sizeRenTrm {Sg : Sig} (M : NomTrm Sg) (ρ : Rn) : (ρ * M).size = M.size := by
  match M with
  | .atom x => rfl
  | .op o bs => simpa using sizeRenArg bs ρ

@[simp] theorem sizeRenArg {Sg : Sig} {ms : List Nat} (bs : NomArg Sg ms) (ρ : Rn) :
    (ρ * bs).size = bs.size := by
  match bs with
  | .nil => rfl
  | .cons b bs' =>
      simp only [rnNomArg_cons, NomArg.size_cons, sizeRenBnd b ρ, sizeRenArg bs' ρ]

@[simp] theorem sizeRenBnd {Sg : Sig} {m : Nat} (b : NomBnd Sg m) (ρ : Rn) :
    (ρ * b).size = b.size := by
  match b with
  | .base M => exact sizeRenTrm M ρ
  | .abs x b' => exact sizeRenBnd b' ρ

end

theorem sizeRenTrmLe {Sg : Sig} {s : Nat} (M : NomTrm Sg) (ρ : Rn) (q : M.size ≤ s) :
    (ρ * M).size ≤ s := by rw [sizeRenTrm]; exact q

theorem sizeRenArgLe {Sg : Sig} {s : Nat} {ms : List Nat} (bs : NomArg Sg ms) (ρ : Rn)
    (q : bs.size ≤ s) : (ρ * bs).size ≤ s := by rw [sizeRenArg]; exact q

theorem sizeRenBndLe {Sg : Sig} {s : Nat} {m : Nat} (b : NomBnd Sg m) (ρ : Rn)
    (q : b.size ≤ s) : (ρ * b).size ≤ s := by rw [sizeRenBnd]; exact q

end Adequacy

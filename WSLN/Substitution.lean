import WSLN.Term

/-!
# Substitution and renaming

Port of `agda-code/agda/WSLN/Sig/Substitution.agda`.

Agda's overloaded `Apply` instances for the action `_*_` become `HMul` instances,
so `σ * t` reads identically.  `Sb` and `Rn` are opaque `def`s rather than
`abbrev`s: both unfold to function types, and reducible aliases would make the
`HMul` instances for substitutions and renamings indistinguishable.

Agda overloads `_∘/_:=_` and `_:=_` through an `Identity`/`UpdateFun` class.  Lean
has no such class here, so each carrier gets its own token: `σ ∘/ x ≔ u` / `x ≔ u`
at substitution type, `ρ ∘/ x ≔ʳ y` / `x ≔ʳ y` at renaming type.
-/

namespace WSLN

/-! ## Substitutions and renamings -/

/-- Agda: `Sb` (WSLN/Sig/Substitution.agda). -/
def Sb (Sg : Sig) : Type := Atom → Trm Sg 0

/-- Agda: `Rn` (WSLN/Sig/Substitution.agda). -/
def Rn : Type := Atom → Atom

/-- Agda: `idˢ` (WSLN/Sig/Substitution.agda). -/
def Sb.id {Sg : Sig} : Sb Sg := fun x => .atom x

/-- Agda: `idʳ` (WSLN/Sig/Substitution.agda). -/
def Rn.id : Rn := fun x => x

/-- Agda: `𝐚∘` (WSLN/Sig/Substitution.agda). Renamings as substitutions. -/
def Sb.ofRn {Sg : Sig} (ρ : Rn) : Sb Sg := fun x => .atom (ρ x)

/-- Composition of renamings; Agda uses the `Composition` instance for functions. -/
def Rn.comp (ρ' ρ : Rn) : Rn := fun x => ρ' (ρ x)

/-- Agda: `_∘/_:=_` at substitution type (WSLN/Atom.agda). -/
def Sb.update {Sg : Sig} (σ : Sb Sg) (x : Atom) (u : Trm Sg 0) : Sb Sg :=
  updateFn σ x u

/-- Agda: `_∘/_:=_` at renaming type (WSLN/Atom.agda). -/
def Rn.update (ρ : Rn) (x y : Atom) : Rn := updateFn ρ x y

/-- Agda: `_:=_` at substitution type. -/
def Sb.single {Sg : Sig} (x : Atom) (u : Trm Sg 0) : Sb Sg := Sb.id.update x u

/-- Agda: `_:=_` at renaming type. -/
def Rn.single (x y : Atom) : Rn := Rn.id.update x y

@[inherit_doc Sb.update]
scoped notation:60 σ:61 " ∘/ " x:61 " ≔ " u:61 => WSLN.Sb.update σ x u
@[inherit_doc Rn.update]
scoped notation:60 ρ:61 " ∘/ " x:61 " ≔ʳ " y:61 => WSLN.Rn.update ρ x y
@[inherit_doc Sb.single] scoped notation:55 x:56 " ≔ " u:56 => WSLN.Sb.single x u
@[inherit_doc Rn.single] scoped notation:55 x:56 " ≔ʳ " y:56 => WSLN.Rn.single x y

section Update

variable {Sg : Sig}

/-- Agda: `:=Eq` (WSLN/Atom.agda), at substitution type. -/
@[simp] theorem Sb.update_eq (σ : Sb Sg) (x : Atom) (u : Trm Sg 0) :
    (σ ∘/ x ≔ u) x = u := updateFn_eq σ x u

/-- Agda: `:=Neq` (WSLN/Atom.agda), at substitution type. -/
theorem Sb.update_neq (σ : Sb Sg) (u : Trm Sg 0) {x y : Atom} (h : x ≠ y) :
    (σ ∘/ x ≔ u) y = σ y := updateFn_neq σ u h

/-- Agda: `:=Eq` (WSLN/Atom.agda), at renaming type. -/
@[simp] theorem Rn.update_eq (ρ : Rn) (x y : Atom) : (ρ ∘/ x ≔ʳ y) x = y :=
  updateFn_eq ρ x y

/-- Agda: `:=Neq` (WSLN/Atom.agda), at renaming type. -/
theorem Rn.update_neq (ρ : Rn) (y : Atom) {x z : Atom} (h : x ≠ z) :
    (ρ ∘/ x ≔ʳ y) z = ρ z := updateFn_neq ρ y h

@[simp] theorem Sb.single_eq (x : Atom) (u : Trm Sg 0) : (x ≔ u) x = u :=
  Sb.update_eq _ _ _

theorem Sb.single_neq (u : Trm Sg 0) {x y : Atom} (h : x ≠ y) :
    (x ≔ u) y = (Sb.id : Sb Sg) y := Sb.update_neq _ _ h

@[simp] theorem Rn.single_eq (x y : Atom) : (x ≔ʳ y) x = y := Rn.update_eq _ _ _

theorem Rn.single_neq (y : Atom) {x z : Atom} (h : x ≠ z) : (x ≔ʳ y) z = z :=
  Rn.update_neq _ _ h

end Update

/-! ## The action on terms -/

mutual

/-- Agda: `actSb` (WSLN/Sig/Substitution.agda). -/
def actSb {Sg : Sig} {n : Nat} (σ : Sb Sg) : Trm Sg n → Trm Sg n
  | .var i => .var i
  | .atom x => (σ x).weaken n (Nat.zero_le n)
  | .op o ts => .op o (actSbArg σ ts)

/-- Agda: `actSb'` (WSLN/Sig/Substitution.agda). -/
def actSbArg {Sg : Sig} {n : Nat} {ms : List Nat} (σ : Sb Sg) :
    Arg Sg n ms → Arg Sg n ms
  | .nil => .nil
  | .cons t ts => .cons (actSb σ t) (actSbArg σ ts)

end

/-- Agda: `ApplySb` (WSLN/Sig/Substitution.agda). -/
instance instHMulSbTrm {Sg : Sig} {n : Nat} : HMul (Sb Sg) (Trm Sg n) (Trm Sg n) :=
  ⟨actSb⟩

/-- Agda: `ApplySb'` (WSLN/Sig/Substitution.agda). -/
instance instHMulSbArg {Sg : Sig} {n : Nat} {ms : List Nat} :
    HMul (Sb Sg) (Arg Sg n ms) (Arg Sg n ms) := ⟨actSbArg⟩

/-- Agda: `ApplyRn` (WSLN/Sig/Substitution.agda).  Renaming is treated as a
special case of substitution. -/
instance instHMulRnTrm {Sg : Sig} {n : Nat} : HMul Rn (Trm Sg n) (Trm Sg n) :=
  ⟨fun ρ t => (Sb.ofRn ρ : Sb Sg) * t⟩

/-- Agda: `ApplyRn'` (WSLN/Sig/Substitution.agda). -/
instance instHMulRnArg {Sg : Sig} {n : Nat} {ms : List Nat} :
    HMul Rn (Arg Sg n ms) (Arg Sg n ms) := ⟨fun ρ ts => (Sb.ofRn ρ : Sb Sg) * ts⟩

@[simp] theorem actSb_var {Sg : Sig} {n : Nat} (σ : Sb Sg) (i : Fin n) :
    σ * (Trm.var i : Trm Sg n) = .var i := rfl

@[simp] theorem actSb_atom {Sg : Sig} {n : Nat} (σ : Sb Sg) (x : Atom) :
    σ * (Trm.atom x : Trm Sg n) = (σ x).weaken n (Nat.zero_le n) := rfl

@[simp] theorem actSb_op {Sg : Sig} {n : Nat} (σ : Sb Sg) (o : Sg.Op)
    (ts : Arg Sg n (Sg.ar o)) : σ * (Trm.op o ts) = .op o (σ * ts) := rfl

@[simp] theorem actSb_nil {Sg : Sig} {n : Nat} (σ : Sb Sg) :
    σ * (Arg.nil : Arg Sg n []) = .nil := rfl

@[simp] theorem actSb_cons {Sg : Sig} {n k : Nat} {ms : List Nat} (σ : Sb Sg)
    (t : Trm Sg (n + k)) (ts : Arg Sg n ms) :
    σ * (Arg.cons t ts) = .cons (σ * t) (σ * ts) := rfl

@[simp] theorem actRn_trm {Sg : Sig} {n : Nat} (ρ : Rn) (t : Trm Sg n) :
    ρ * t = (Sb.ofRn ρ : Sb Sg) * t := rfl

@[simp] theorem actRn_arg {Sg : Sig} {n : Nat} {ms : List Nat} (ρ : Rn)
    (ts : Arg Sg n ms) : ρ * ts = (Sb.ofRn ρ : Sb Sg) * ts := rfl

/-! ## Updated renamings -/

/-- Agda: `updateRen` (WSLN/Sig/Substitution.agda). -/
theorem updateRen {Sg : Sig} (ρ : Rn) (x x' y : Atom) :
    ((Sb.ofRn ρ : Sb Sg) ∘/ x ≔ (Trm.atom x' : Trm Sg 0)) y
      = (Sb.ofRn (ρ ∘/ x ≔ʳ x') : Sb Sg) y := by
  by_cases h : x = y
  · subst h; simp [Sb.ofRn]
  · rw [Sb.update_neq _ _ h]
    show (Trm.atom (ρ y) : Trm Sg 0) = Trm.atom ((ρ ∘/ x ≔ʳ x') y)
    rw [Rn.update_neq _ _ h]

/-- Agda: `updateRen²` (WSLN/Sig/Substitution.agda). -/
theorem updateRen₂ {Sg : Sig} (ρ : Rn) (x x' y y' z : Atom) :
    (((Sb.ofRn ρ : Sb Sg) ∘/ x ≔ (Trm.atom x' : Trm Sg 0)) ∘/ y ≔ (Trm.atom y' : Trm Sg 0)) z
      = (Sb.ofRn ((ρ ∘/ x ≔ʳ x') ∘/ y ≔ʳ y') : Sb Sg) z := by
  by_cases h : y = z
  · subst h; simp [Sb.ofRn]
  · rw [Sb.update_neq _ _ h]
    show _ = (Trm.atom (((ρ ∘/ x ≔ʳ x') ∘/ y ≔ʳ y') z) : Trm Sg 0)
    rw [Rn.update_neq _ _ h]
    exact updateRen ρ x x' z

/-! ## Substitution respects support -/

mutual

/-- Agda: `sbRespSupp` (WSLN/Sig/Substitution.agda). -/
theorem sbRespSupp {Sg : Sig} {n : Nat} (σ σ' : Sb Sg) (t : Trm Sg n)
    (e : ∀ x, x ∈ supp t → σ x = σ' x) : σ * t = σ' * t := by
  match t with
  | .var i => rfl
  | .atom x => simp [e x Fset.Mem.single]
  | .op o ts => simpa using sbRespSuppArg σ σ' ts e

/-- Agda: `sbRespSupp'` (WSLN/Sig/Substitution.agda). -/
theorem sbRespSuppArg {Sg : Sig} {n : Nat} {ms : List Nat} (σ σ' : Sb Sg)
    (ts : Arg Sg n ms) (e : ∀ x, x ∈ supp ts → σ x = σ' x) : σ * ts = σ' * ts := by
  match ts with
  | .nil => rfl
  | .cons t us =>
      simp only [actSb_cons, Arg.cons.injEq]
      exact ⟨sbRespSupp σ σ' t (fun x hx => e x (Fset.Mem.unionL hx)),
        sbRespSuppArg σ σ' us (fun x hx => e x (Fset.Mem.unionR hx))⟩

end

/-- Agda: `rnRespSupp` (WSLN/Sig/Substitution.agda). -/
theorem rnRespSupp {Sg : Sig} {n : Nat} (ρ ρ' : Rn) (t : Trm Sg n)
    (e : ∀ x, x ∈ supp t → ρ x = ρ' x) : ρ * t = ρ' * t :=
  sbRespSupp (Sb.ofRn ρ) (Sb.ofRn ρ') t fun x hx => by
    show (Trm.atom (ρ x) : Trm Sg 0) = Trm.atom (ρ' x)
    rw [e x hx]

/-! ## Composition -/

/-- Agda: `_∘ˢ_` (WSLN/Sig/Substitution.agda). -/
def Sb.comp {Sg : Sig} (σ' σ : Sb Sg) : Sb Sg := fun x => σ' * σ x

@[inherit_doc Sb.comp] scoped infixr:90 " ∘ˢ " => WSLN.Sb.comp

@[simp] theorem Sb.comp_apply {Sg : Sig} (σ' σ : Sb Sg) (x : Atom) :
    (σ' ∘ˢ σ) x = σ' * σ x := rfl

/-! ## Substitution respects scope extension -/

mutual

/-- Agda: `sb‿` (WSLN/Sig/Substitution.agda). -/
theorem sbWeaken {Sg : Sig} {m : Nat} (t : Trm Sg m) (n : Nat) (h : m ≤ n) (σ : Sb Sg) :
    σ * (t.weaken n h) = (σ * t).weaken n h := by
  match t with
  | .var i => rfl
  | .atom x =>
      simp only [Trm.weaken_atom, actSb_atom]
      exact (Trm.weaken_trans (σ x) m n (Nat.zero_le m) h (Nat.zero_le n)).symm
  | .op o ts => simpa using sbWeakenArg ts n h σ

/-- Agda: `sb‿'` (WSLN/Sig/Substitution.agda). -/
theorem sbWeakenArg {Sg : Sig} {m : Nat} {ms : List Nat} (ts : Arg Sg m ms) (n : Nat)
    (h : m ≤ n) (σ : Sb Sg) : σ * (ts.weaken n h) = (σ * ts).weaken n h := by
  match ts with
  | .nil => rfl
  | .cons (m := k) t us =>
      simp only [Arg.weaken_cons, actSb_cons, Arg.cons.injEq]
      exact ⟨sbWeaken t (n + k) (by omega) σ, sbWeakenArg us n h σ⟩

end

/-- Agda: `rn‿` (WSLN/Sig/Substitution.agda). -/
theorem rnWeaken {Sg : Sig} {m : Nat} (t : Trm Sg m) (n : Nat) (h : m ≤ n) (ρ : Rn) :
    ρ * (t.weaken n h) = (ρ * t).weaken n h :=
  sbWeaken t n h (Sb.ofRn ρ)

/-! ## Unit and associativity laws -/

mutual

/-- Agda: `sbUnit` (WSLN/Sig/Substitution.agda). -/
@[simp] theorem sbUnit {Sg : Sig} {n : Nat} (t : Trm Sg n) :
    (Sb.id : Sb Sg) * t = t := by
  match t with
  | .var i => rfl
  | .atom x => rfl
  | .op o ts => simpa using sbUnitArg ts

/-- Agda: `sbUnit'` (WSLN/Sig/Substitution.agda). -/
@[simp] theorem sbUnitArg {Sg : Sig} {n : Nat} {ms : List Nat} (ts : Arg Sg n ms) :
    (Sb.id : Sb Sg) * ts = ts := by
  match ts with
  | .nil => rfl
  | .cons t us =>
      simp only [actSb_cons, Arg.cons.injEq]
      exact ⟨sbUnit t, sbUnitArg us⟩

end

mutual

/-- Agda: `sbAssoc` (WSLN/Sig/Substitution.agda). -/
theorem sbAssoc {Sg : Sig} {n : Nat} (σ σ' : Sb Sg) (t : Trm Sg n) :
    (σ' ∘ˢ σ) * t = σ' * (σ * t) := by
  match t with
  | .var i => rfl
  | .atom x =>
      simp only [actSb_atom, Sb.comp_apply]
      exact (sbWeaken (σ x) n (Nat.zero_le n) σ').symm
  | .op o ts => simpa using sbAssocArg σ σ' ts

/-- Agda: `sbAssoc'` (WSLN/Sig/Substitution.agda). -/
theorem sbAssocArg {Sg : Sig} {n : Nat} {ms : List Nat} (σ σ' : Sb Sg)
    (ts : Arg Sg n ms) : (σ' ∘ˢ σ) * ts = σ' * (σ * ts) := by
  match ts with
  | .nil => rfl
  | .cons t us =>
      simp only [actSb_cons, Arg.cons.injEq]
      exact ⟨sbAssoc σ σ' t, sbAssocArg σ σ' us⟩

end

/-- Agda: `rnUnit` (WSLN/Sig/Substitution.agda). -/
theorem rnUnit {Sg : Sig} {n : Nat} (t : Trm Sg n) : Rn.id * t = t := sbUnit (Sg := Sg) t

/-- Agda: `rnAssoc` (WSLN/Sig/Substitution.agda). -/
theorem rnAssoc {Sg : Sig} {n : Nat} (ρ ρ' : Rn) (t : Trm Sg n) :
    Rn.comp ρ' ρ * t = ρ' * (ρ * t) :=
  sbAssoc (Sb.ofRn ρ) (Sb.ofRn ρ') t

/-! ## Updating substitutions and renamings -/

/-- Agda: `updateEq` (WSLN/Sig/Substitution.agda). -/
@[simp] theorem updateEq {Sg : Sig} (σ : Sb Sg) (t : Trm Sg 0) (x : Atom) :
    (σ ∘/ x ≔ t) * (Trm.atom x : Trm Sg 0) = t := by simp

/-- Agda: `updateFresh` (WSLN/Sig/Substitution.agda). -/
theorem updateFresh {Sg : Sig} {n : Nat} (σ : Sb Sg) (x : Atom) (u : Trm Sg 0)
    (t : Trm Sg n) (h : x # t) : (σ ∘/ x ≔ u) * t = σ * t :=
  sbRespSupp _ σ t fun _ hy =>
    Sb.update_neq σ u fun e => Fset.not_mem_of_notMem h (e ▸ hy)

/-- Agda: `updateIdSb` (WSLN/Sig/Substitution.agda). -/
theorem updateIdSb {Sg : Sig} {n : Nat} (x : Atom) (t : Trm Sg n) :
    (x ≔ (Trm.atom x : Trm Sg 0)) * t = t := by
  have e : (x ≔ (Trm.atom x : Trm Sg 0)) * t = (Sb.id : Sb Sg) * t :=
    sbRespSupp _ Sb.id t fun x' _ => updateFn_id Sb.id x x'
  rw [e, sbUnit]

/-- Agda: `ssbFresh` (WSLN/Sig/Substitution.agda). -/
theorem ssbFresh {Sg : Sig} {n : Nat} (x : Atom) (u : Trm Sg 0) (t : Trm Sg n)
    (h : x # t) : (x ≔ u) * t = t := by
  rw [show (x ≔ u) = ((Sb.id : Sb Sg) ∘/ x ≔ u) from rfl,
    updateFresh Sb.id x u t h, sbUnit]

/-- Agda: `updateRn` (WSLN/Sig/Substitution.agda). -/
theorem updateRn {Sg : Sig} {n : Nat} (ρ : Rn) (x x' : Atom) (t : Trm Sg n) :
    ((Sb.ofRn ρ : Sb Sg) ∘/ x ≔ (Trm.atom x' : Trm Sg 0)) * t
      = (Sb.ofRn (ρ ∘/ x ≔ʳ x') : Sb Sg) * t :=
  sbRespSupp _ _ t fun y _ => updateRen ρ x x' y

/-- Agda: `updateRn²` (WSLN/Sig/Substitution.agda). -/
theorem updateRn₂ {Sg : Sig} {n : Nat} (ρ : Rn) (x x' y y' : Atom) (t : Trm Sg n) :
    (((Sb.ofRn ρ : Sb Sg) ∘/ x ≔ (Trm.atom x' : Trm Sg 0)) ∘/ y ≔ (Trm.atom y' : Trm Sg 0)) * t
      = (Sb.ofRn ((ρ ∘/ x ≔ʳ x') ∘/ y ≔ʳ y') : Sb Sg) * t :=
  sbRespSupp _ _ t fun z _ => updateRen₂ ρ x x' y y' z

/-- Agda: `updateId` (WSLN/Sig/Substitution.agda). -/
theorem updateId {Sg : Sig} {n : Nat} (x : Atom) (t : Trm Sg n) :
    ((x ≔ʳ x) : Rn) * t = t := by
  have e : ((x ≔ʳ x) : Rn) * t = Rn.id * t :=
    rnRespSupp (Sg := Sg) _ Rn.id t fun x' _ => updateFn_id Rn.id x x'
  rw [e, rnUnit]

/-- Agda: `updateFreshRn` (WSLN/Sig/Substitution.agda). -/
theorem updateFreshRn {Sg : Sig} {n : Nat} (ρ : Rn) (x y : Atom) (t : Trm Sg n)
    (h : x # t) : ((ρ ∘/ x ≔ʳ y) : Rn) * t = ρ * t := by
  show (Sb.ofRn (ρ ∘/ x ≔ʳ y) : Sb Sg) * t = (Sb.ofRn ρ : Sb Sg) * t
  rw [← updateRn (Sg := Sg) ρ x y t]
  exact updateFresh (Sb.ofRn ρ) x (Trm.atom y) t h

end WSLN

import Adequacy.Translation

/-!
# Capture-avoiding substitution for nameful terms

Port of `agda-code/agda/Adequacy/Substitution.agda`.

Cf. Allen Stoughton, *Substitution Revisited*, Theoretical Computer Science
59 (1988) 317–325.

Translation carries simultaneous capture-avoiding nameful substitution exactly onto
the locally nameless substitution action.

Agda's `Apply`/`Identity` instances become `HMul` instances and `NomSb.id`; the
overloaded `σ ∘/ x := M` and `x := M` get the project-standard per-carrier tokens
`σ ∘/ x ≔ⁿ M` and `x ≔ⁿ M`.
-/

namespace Adequacy

open WSLN

/-! ## Nameful substitutions -/

/-- Lean-specific: the type of nameful substitutions.  The Agda source writes
`𝔸 → NomTrm` inline; an opaque `def` (as for `WSLN.Sb`) keeps the `HMul` instances
for nameful substitution and for renaming distinguishable. -/
def NomSb (Sg : Sig) : Type := Atom → NomTrm Sg

/-- Agda: `IdentityNomSb` (Adequacy/Substitution.agda). -/
def NomSb.id {Sg : Sig} : NomSb Sg := fun x => .atom x

/-- Agda's overloaded `_∘/_:=_` (WSLN/Atom.agda) at nameful substitution type. -/
def NomSb.update {Sg : Sig} (σ : NomSb Sg) (x : Atom) (M : NomTrm Sg) : NomSb Sg :=
  updateFn σ x M

/-- Agda's overloaded `_:=_` (WSLN/Atom.agda) at nameful substitution type. -/
def NomSb.single {Sg : Sig} (x : Atom) (M : NomTrm Sg) : NomSb Sg :=
  NomSb.id.update x M

@[inherit_doc NomSb.update]
scoped notation:60 σ:61 " ∘/ " x:61 " ≔ⁿ " M:61 => Adequacy.NomSb.update σ x M
@[inherit_doc NomSb.single]
scoped notation:55 x:56 " ≔ⁿ " M:56 => Adequacy.NomSb.single x M

/-! ## Capture-avoiding substitution -/

/-- Lean-specific: the deterministic binder name chosen by `actNomSbBnd`, factored
out so that the definition and the `mulCorrectBnd` proof use syntactically the same
expression.  Agda: `new (⋃ (supp ∘ σ) (supp b))`. -/
def newBinder {Sg : Sig} (σ : NomSb Sg) {m : Nat} (b : NomBnd Sg m) : Atom :=
  Fset.new (Fset.bigUnion (fun z => supp (σ z)) (supp b))

mutual

/-- Agda: `actNomSb` (Adequacy/Substitution.agda). -/
def actNomSb {Sg : Sig} (σ : NomSb Sg) : NomTrm Sg → NomTrm Sg
  | .atom x => σ x
  | .op o bs => .op o (actNomSbArg σ bs)

/-- Agda: `actNomSbᵃ` (Adequacy/Substitution.agda). -/
def actNomSbArg {Sg : Sig} {ms : List Nat} (σ : NomSb Sg) : NomArg Sg ms → NomArg Sg ms
  | .nil => .nil
  | .cons b bs => .cons (actNomSbBnd σ b) (actNomSbArg σ bs)

/-- Agda: `actNomSbᵇ` (Adequacy/Substitution.agda).  Every binder is freshened
against the substitution's range on the binder's support, and against the binder. -/
def actNomSbBnd {Sg : Sig} {m : Nat} (σ : NomSb Sg) : NomBnd Sg m → NomBnd Sg m
  | .base M => .base (actNomSb σ M)
  | .abs x b =>
      .abs (newBinder σ b) (actNomSbBnd (σ.update x (.atom (newBinder σ b))) b)

end

/-- Agda: `ApplyNomSb` (Adequacy/Substitution.agda). -/
instance instHMulNomSbNomTrm {Sg : Sig} : HMul (NomSb Sg) (NomTrm Sg) (NomTrm Sg) :=
  ⟨actNomSb⟩

/-- Agda: `ApplyNomSbᵃ` (Adequacy/Substitution.agda). -/
instance instHMulNomSbNomArg {Sg : Sig} {ms : List Nat} :
    HMul (NomSb Sg) (NomArg Sg ms) (NomArg Sg ms) := ⟨actNomSbArg⟩

/-- Agda: `ApplyNomSbᵇ` (Adequacy/Substitution.agda). -/
instance instHMulNomSbNomBnd {Sg : Sig} {m : Nat} :
    HMul (NomSb Sg) (NomBnd Sg m) (NomBnd Sg m) := ⟨actNomSbBnd⟩

@[simp] theorem mulNom_atom {Sg : Sig} (σ : NomSb Sg) (x : Atom) :
    σ * (NomTrm.atom x : NomTrm Sg) = σ x := rfl

@[simp] theorem mulNom_op {Sg : Sig} (σ : NomSb Sg) (o : Sg.Op)
    (bs : NomArg Sg (Sg.ar o)) : σ * (NomTrm.op o bs) = .op o (σ * bs) := rfl

@[simp] theorem mulNomArg_nil {Sg : Sig} (σ : NomSb Sg) :
    σ * (NomArg.nil : NomArg Sg []) = .nil := rfl

@[simp] theorem mulNomArg_cons {Sg : Sig} {m : Nat} {ms : List Nat} (σ : NomSb Sg)
    (b : NomBnd Sg m) (bs : NomArg Sg ms) :
    σ * (NomArg.cons b bs) = .cons (σ * b) (σ * bs) := rfl

@[simp] theorem mulNomBnd_base {Sg : Sig} (σ : NomSb Sg) (M : NomTrm Sg) :
    σ * (NomBnd.base M) = .base (σ * M) := rfl

@[simp] theorem mulNomBnd_abs {Sg : Sig} {m : Nat} (σ : NomSb Sg) (x : Atom)
    (b : NomBnd Sg m) :
    σ * (NomBnd.abs x b)
      = .abs (newBinder σ b)
          ((σ ∘/ x ≔ⁿ NomTrm.atom (newBinder σ b)) * b) := rfl

/-! ## Substitution correctness -/

mutual

/-- Agda: `*correct` (Adequacy/Substitution.agda). -/
theorem mulCorrect {Sg : Sig} (σ : NomSb Sg) (M : NomTrm Sg) :
    toWS (σ * M) = toWSSb σ * toWS M := by
  match M with
  | .atom x =>
      show toWS (σ x) = toWSSb σ * (Trm.atom x : Trm Sg 0)
      rw [actSb_atom]
      show toWS (σ x) = (toWS (σ x)).weaken 0 (Nat.zero_le 0)
      rw [Trm.weaken_self]
  | .op o bs => exact congrArg (Trm.op o) (mulCorrectArg σ bs)

/-- Agda: `*correctᵃ` (Adequacy/Substitution.agda). -/
theorem mulCorrectArg {Sg : Sig} {ms : List Nat} (σ : NomSb Sg) (bs : NomArg Sg ms) :
    toWSArg (σ * bs) = toWSSb σ * toWSArg bs := by
  match bs with
  | .nil => rfl
  | .cons (m := m) b bs' =>
      show Arg.cons (Trm.castScope (Nat.zero_add m).symm (toWSBnd (σ * b)))
            (toWSArg (σ * bs'))
          = Arg.cons (toWSSb σ * Trm.castScope (Nat.zero_add m).symm (toWSBnd b))
            (toWSSb σ * toWSArg bs')
      rw [Arg.cons.injEq]
      exact ⟨
        (congrArg (Trm.castScope (Nat.zero_add m).symm) (mulCorrectBnd σ b)).trans
          (actSb_castScope (toWSSb σ) (Nat.zero_add m).symm (toWSBnd b)).symm,
        mulCorrectArg σ bs'⟩

/-- Agda: `*correctᵇ` (Adequacy/Substitution.agda). -/
theorem mulCorrectBnd {Sg : Sig} {m : Nat} (σ : NomSb Sg) (b : NomBnd Sg m) :
    toWSBnd (σ * b) = toWSSb σ * toWSBnd b := by
  match b with
  | .base M => exact mulCorrect σ M
  | .abs x b' =>
      have hf : ∀ z, z ∈ supp (toWSBnd b') → ¬ (x = z) →
          newBinder σ b' # (toWSSb σ) z := by
        intro z hz _
        exact Fset.subset_notMem
          (Fset.subset_trans (toWS_supp (σ z))
            (Fset.subset_bigUnion (fun w => supp (σ w)) (toWSBnd_supp b' hz)))
          (Fset.new_notMem _)
      simp only [mulNomBnd_abs, toWSBnd_abs]
      calc (newBinder σ b' ． toWSBnd ((σ ∘/ x ≔ⁿ NomTrm.atom (newBinder σ b')) * b'))
          = (newBinder σ b' ．
              toWSSb (σ ∘/ x ≔ⁿ NomTrm.atom (newBinder σ b')) * toWSBnd b') := by
              rw [mulCorrectBnd (σ ∘/ x ≔ⁿ NomTrm.atom (newBinder σ b')) b']
        _ = (newBinder σ b' ．
              ((toWSSb σ) ∘/ x ≔ (Trm.atom (newBinder σ b') : Trm Sg 0)) * toWSBnd b') := by
              rw [sbRespSupp (toWSSb (σ ∘/ x ≔ⁿ NomTrm.atom (newBinder σ b')))
                ((toWSSb σ) ∘/ x ≔ (Trm.atom (newBinder σ b') : Trm Sg 0)) (toWSBnd b')
                (fun z _ => toWSSb_update σ (NomTrm.atom (newBinder σ b')) x z)]
        _ = toWSSb σ * (x ． toWSBnd b') :=
              (sbAbs (toWSSb σ) x (newBinder σ b') (toWSBnd b') hf).symm

end

/-- Agda: `:=correct` (Adequacy/Substitution.agda). -/
theorem updateCorrect {Sg : Sig} (M : NomTrm Sg) (x : Atom) (N : NomTrm Sg) :
    toWS ((x ≔ⁿ M) * N) = ((x ≔ toWS M) : Sb Sg) * toWS N :=
  (mulCorrect (x ≔ⁿ M) N).trans
    (sbRespSupp (toWSSb (x ≔ⁿ M)) (x ≔ toWS M) (toWS N)
      (fun y _ => toWSSb_update NomSb.id M x y))

end Adequacy

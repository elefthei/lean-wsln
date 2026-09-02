import MLTT.Syntax

/-!
# Forms of judgement

Port of `agda-code/agda/MLTT/Judgement.agda`.
-/

namespace MLTT

open WSLN

/-! ## Forms of judgement -/

inductive Jg : Type where
  /-- Well-formed term of a given type and level. -/
  | ty (a : Tm0) (A : Ty0) (l : Lvl) : Jg
  /-- Conversion between terms of a given type and level. -/
  | eq (a a' : Tm0) (A : Ty0) (l : Lvl) : Jg

@[inherit_doc Jg.ty]
scoped notation:40 a:41 " ∶ " A:41 " ⦂ " l:41 => MLTT.Jg.ty a A l
@[inherit_doc Jg.eq]
scoped notation:40 a:41 " ＝ " a':41 " ∶ " A:41 " ⦂ " l:41 => MLTT.Jg.eq a a' A l

/-- `A` is a type at level `l`. -/
def Jg.isTy (A : Ty0) (l : Lvl) : Jg := .ty A (U l) (l + 1)

@[inherit_doc Jg.isTy]
scoped notation:40 A:41 " ⦂ " l:41 => MLTT.Jg.isTy A l

/-- `A ＝ A' ⦂ l`: type conversion at level `l`, as a judgement. -/
def Jg.tyEq (A A' : Ty0) (l : Lvl) : Jg := .eq A A' (U l) (l + 1)

@[inherit_doc Jg.tyEq]
scoped notation:40 A:41 " ＝ " A':41 " ⦂ " l:41 => MLTT.Jg.tyEq A A' l

/-! ## Support of judgements -/

/-- The union in the conversion case is right-nested, mirroring Agda's `infixr 6 _∪_`. -/
def suppJg : Jg → Fset
  | .ty a A _ => supp a ∪ supp A
  | .eq a a' A _ => supp a ∪ (supp a' ∪ supp A)

instance instFiniteSupportJg : FiniteSupport Jg := ⟨suppJg⟩

@[simp] theorem supp_ty (a : Tm0) (A : Ty0) (l : Lvl) :
    supp (a ∶ A ⦂ l) = supp a ∪ supp A := rfl

@[simp] theorem supp_eq (a a' : Tm0) (A : Ty0) (l : Lvl) :
    supp (a ＝ a' ∶ A ⦂ l) = supp a ∪ (supp a' ∪ supp A) := rfl

/-! ## Action of substitutions on judgements -/

def actSbJg (σ : Sb sig) : Jg → Jg
  | .ty a A l => .ty (σ * a) (σ * A) l
  | .eq a a' A l => .eq (σ * a) (σ * a') (σ * A) l

instance instHMulSbJg : HMul (Sb sig) Jg Jg := ⟨actSbJg⟩

instance instHMulRnJg : HMul Rn Jg Jg := ⟨fun ρ J => (Sb.ofRn ρ : Sb sig) * J⟩

@[simp] theorem actSbJg_ty (σ : Sb sig) (a : Tm0) (A : Ty0) (l : Lvl) :
    σ * (a ∶ A ⦂ l) = (σ * a ∶ σ * A ⦂ l) := rfl

@[simp] theorem actSbJg_eq (σ : Sb sig) (a a' : Tm0) (A : Ty0) (l : Lvl) :
    σ * (a ＝ a' ∶ A ⦂ l) = (σ * a ＝ σ * a' ∶ σ * A ⦂ l) := rfl

@[simp] theorem actRnJg (ρ : Rn) (J : Jg) : ρ * J = (Sb.ofRn ρ : Sb sig) * J := rfl

theorem jgRespSupp (σ σ' : Sb sig) (J : Jg) (e : ∀ x, x ∈ supp J → σ x = σ' x) :
    σ * J = σ' * J := by
  match J with
  | .ty a A l =>
      rw [actSbJg_ty, actSbJg_ty,
        sbRespSupp σ σ' a fun _ p => e _ (Fset.Mem.unionL p),
        sbRespSupp σ σ' A fun _ p => e _ (Fset.Mem.unionR p)]
  | .eq a a' A l =>
      rw [actSbJg_eq, actSbJg_eq,
        sbRespSupp σ σ' a fun _ p => e _ (Fset.Mem.unionL p),
        sbRespSupp σ σ' a' fun _ p => e _ (Fset.Mem.unionR (Fset.Mem.unionL p)),
        sbRespSupp σ σ' A fun _ p => e _ (Fset.Mem.unionR (Fset.Mem.unionR p))]

@[simp] theorem sbUnitJg (J : Jg) : (Sb.id : Sb sig) * J = J := by
  match J with
  | .ty a A l => rw [actSbJg_ty, sbUnit, sbUnit]
  | .eq a a' A l => rw [actSbJg_eq, sbUnit, sbUnit, sbUnit]

theorem rnUnitJg (J : Jg) : Rn.id * J = J := sbUnitJg J

/-! ## Operations on judgements -/

def Jg.ty₁ : Jg → Jg
  | .ty a A l => .ty a A l
  | .eq a _ A l => .ty a A l

def Jg.ty₂ : Jg → Jg
  | .ty a A l => .ty a A l
  | .eq _ a A l => .ty a A l

end MLTT

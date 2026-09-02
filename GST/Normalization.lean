import GST.LogicalRelation
import GST.Sound

/-!
# Normalization

Port of `agda-code/agda/GST/Normalization.agda`.

`nf Γ q` is the normal form of the term typed by `q`, obtained by reifying its value
at the initial environment.  `NF1` and `NF2` are the two halves of "convertible iff
equal normal forms"; the names come from D. Čubrić, P. Dybjer and P. Scott,
*Normalization and the Yoneda embedding* (Math. Struct. in Comp. Science 8 (1998)
153–192), section 1.1, as in the Agda source.
-/

namespace GST

open WSLN

def nf {A : Ty} {a : Tm0} {S : Fset} (Γ : Cx S) (q : Γ ⊢ a ∶ A) : Tm0 :=
  reifyTm A (sem₀ q (env₀ Γ))

def nfNf {A : Ty} {a : Tm0} {S : Fset} (Γ : Cx S) (q : Γ ⊢ a ∶ A) : Γ ⊢ⁿ nf Γ q ∶ A :=
  reifyNf (sem₀ q (env₀ Γ))

def NF1 {A : Ty} {a : Tm0} {S : Fset} (Γ : Cx S) (q : Γ ⊢ a ∶ A) :
    Γ ⊢ a ＝ nf Γ q ∶ A :=
  castEq (sbUnit a) rfl (glueReify (FP q (FPSb₀ Γ)))

def NF1' {A : Ty} {a a' : Tm0} {S : Fset} (Γ : Cx S) (q : Γ ⊢ a ∶ A) (q' : Γ ⊢ a' ∶ A)
    (e : nf Γ q = nf Γ q') : Γ ⊢ a ＝ a' ∶ A :=
  .trans (castEq rfl e (NF1 Γ q)) (.symm (NF1 Γ q'))

theorem NF2 {A : Ty} {a a' : Tm0} {S : Fset} (Γ : Cx S) (q : Γ ⊢ a ∶ A)
    (q' : Γ ⊢ a' ∶ A) (q'' : Γ ⊢ a ＝ a' ∶ A) : nf Γ q = nf Γ q' :=
  (reify A).hom.resp (sound q q' q'' (env₀ Γ))

end GST

import Adequacy
import Examples.Lambda

/-!
# Adequacy, checked on concrete λ-terms

The adequacy statements of `Adequacy/Translation.lean` are proved for an arbitrary
binding signature, so they cannot be instantiated inside `Adequacy/` itself (that
would require importing a concrete signature).  These `example`s instantiate them at
`Lambda.sig` and gate the build.
-/

namespace Examples.AdequacyChecks

open WSLN Adequacy Lambda

/-- The nameful identity function `λ z. z`, with binder name `7`. -/
def nomId : NomTrm sig := .op Op.lm (.cons (.abs 7 (.base (.atom 7))) .nil)

/-- The same term with binder name `9`; α-equivalent to `nomId`. -/
def nomId' : NomTrm sig := .op Op.lm (.cons (.abs 9 (.base (.atom 9))) .nil)

/-- The locally nameless identity function. -/
def lnId : Tm 0 := 𝛌 i0

-- Translation erases the binder name.  It is structurally recursive, so this `rfl`
-- is checked by kernel reduction.
example : toWS nomId = lnId := rfl

-- Soundness/injectivity: equal translations means α-equivalent nameful terms.
example : nomId ~ nomId' := injective nomId nomId' rfl

-- Right inverse: `⟦ ⟦t⟧⁻¹ ⟧ ≡ t`.
example : toWS (toNom lnId) = lnId := bijection lnId

-- `toNom` is defined by well-founded recursion, so the kernel cannot reduce it;
-- the compiler can, and `#guard` fails the build if the round trip is not `true`.
#guard toWS (toNom lnId) = lnId

-- Left inverse, modulo α-equivalence.
example : toNom (toWS nomId) ~ nomId := bijection₂ nomId

/-- A nameful term with a free name to substitute for. -/
def nomK : NomTrm sig := .op Op.lm (.cons (.abs 7 (.base (.atom 3))) .nil)

-- Single-name capture-avoiding substitution commutes with translation.
example :
    toWS ((3 ≔ⁿ (NomTrm.atom 5 : NomTrm sig)) * nomK)
      = ((3 ≔ (Trm.atom 5 : Trm sig 0)) : Sb sig) * toWS nomK :=
  updateCorrect (NomTrm.atom 5) 3 nomK

end Examples.AdequacyChecks

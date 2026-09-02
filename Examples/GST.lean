import GST

/-!
# Gödel's System T at work

Concrete instances of the `GST` development: a typing derivation built from the
rules, and the decision procedures and the normalizer run on closed terms.

The deciders and the normalizer recurse over derivations and presheaf data, which the
kernel cannot reduce cheaply, so their results are checked with `#guard` (compiler
evaluation), exactly as `Examples/Adequacy.lean` checks `toNom`.
-/

namespace Examples.GSTExamples

open WSLN GST

/-! ## A typing derivation -/

/-- `0` is fresh for the empty context. -/
private theorem zeroFresh : (0 : Atom) ∉ᶠ (∅ : Fset) := .empty

/-- The identity function on ℕ applied to zero is a natural number:
`◇ ⊢ (𝛌 𝐍𝐚𝐭 i0) ∙ 𝐳𝐞𝐫𝐨 ∶ 𝐍𝐚𝐭`.  The λ-rule is the exists-fresh one, discharged at
the atom `0`. -/
def idAppZero : ◇ ⊢ (𝛌 𝐍𝐚𝐭 (i0 : Tm 1)) ∙ 𝐳𝐞𝐫𝐨 ∶ 𝐍𝐚𝐭 :=
  .app (.lam (x := 0) (h := zeroFresh) (.var .new) .empty) .zero

/-! ## Deciding typing -/

-- The same term is typed by the decision procedure.
#guard (tyDec ◇ 𝐍𝐚𝐭 ((𝛌 𝐍𝐚𝐭 (i0 : Tm 1)) ∙ 𝐳𝐞𝐫𝐨)).isYes

-- `𝐳𝐞𝐫𝐨` is not a function.
#guard !(tyDec ◇ (𝐍𝐚𝐭 ⇒ 𝐍𝐚𝐭) 𝐳𝐞𝐫𝐨).isYes

/-! ## Deciding conversion -/

-- β-conversion is decided positively: `(𝛌 x. x) 0 ＝ 0`.
#guard (convDec ◇ 𝐍𝐚𝐭 ((𝛌 𝐍𝐚𝐭 (i0 : Tm 1)) ∙ 𝐳𝐞𝐫𝐨) 𝐳𝐞𝐫𝐨).isYes

-- Distinct numerals are not convertible.
#guard !(convDec ◇ 𝐍𝐚𝐭 𝐳𝐞𝐫𝐨 (𝐬𝐮𝐜𝐜 𝐳𝐞𝐫𝐨)).isYes

-- η/β-conversion under a binder: `𝛌 x. x ＝ 𝛌 x. (𝛌 y. y) x`.
#guard (convDec ◇ (𝐍𝐚𝐭 ⇒ 𝐍𝐚𝐭) (𝛌 𝐍𝐚𝐭 (i0 : Tm 1))
  (𝛌 𝐍𝐚𝐭 ((𝛌 𝐍𝐚𝐭 (i0 : Tm 2)) ∙ (i0 : Tm 1)))).isYes

/-! ## Normalization -/

-- The normal form of `(𝛌 x. x) 0` is `0`.
#guard nf ◇ idAppZero = 𝐳𝐞𝐫𝐨

end Examples.GSTExamples

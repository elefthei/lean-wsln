import Adequacy.Nameful
import Adequacy.Translation
import Adequacy.Substitution

/-!
# Adequacy

Lean 4 port of `agda-code/agda/Adequacy/*.agda`: locally nameless terms over a
binding signature are in bijection with α-equivalence classes of *nameful* terms
over the same signature, and the bijection carries capture-avoiding nameful
substitution to the locally nameless substitution action.

Agda: `Adequacy` (Adequacy.agda).
-/

/-
# Martin-Löf type theory in the WSLN representation

Lean 4 port of `agda-code/agda/MLTT.agda` and the modules it re-exports:
syntax, judgements, the cofinite rules, and the metatheory (well-scopedness,
weakening, substitution, admissible rules, exists-fresh rules, uniqueness of types).
-/
import MLTT.Syntax
import MLTT.Judgement
import MLTT.Cofinite
import MLTT.Ok
import MLTT.WellScoped
import MLTT.Weakening
import MLTT.Substitution
import MLTT.Admissible
import MLTT.ExistsFresh
import MLTT.Uniqueness

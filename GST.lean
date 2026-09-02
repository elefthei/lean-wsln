import GST.Syntax
import GST.Context
import GST.TypeSystem
import GST.WellScoped
import GST.Setoid
import GST.Renaming
import GST.Substitution
import GST.Admissible
import GST.UniqueTypes
import GST.NormalForm
import GST.Presheaf
import GST.TypeSemantics
import GST.ReifyReflect
import GST.TermSemantics
import GST.LogicalRelation
import GST.Sound
import GST.Normalization
import GST.DecidableConv

/-!
# Gödel's System T

Lean 4 port of `agda-code/agda/GST.agda` and the modules it re-exports: decidability
of βη-conversion for Gödel's System T in the well-scoped locally nameless
representation, proved by normalization by evaluation.
-/

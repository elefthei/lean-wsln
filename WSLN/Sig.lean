import WSLN.Fresh

/-!
# Binding signatures

Port of `agda-code/agda/WSLN/Sig/Sig.agda`.

Agda declares the signature as an instance argument `⦃ Σ : Sig ⦄`; here it is an
explicit parameter (written `Sg`, since `Σ` is a reserved token in Lean), so that
several signatures — the λ-calculus, the π-calculus and MLTT — can coexist in one
build without instance-coherence problems.
-/

namespace WSLN

/-- Agda: `Sig` (WSLN/Sig/Sig.agda). Plotkin's binding signatures. -/
structure Sig where
  /-- Agda: `Op`. The operators of the signature. -/
  Op : Type
  /-- Agda: `ar`. The arity of an operator: one binding depth per argument. -/
  ar : Op → List Nat

end WSLN

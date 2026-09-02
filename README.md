# lean-wsln

A Lean 4 formalization of Andrew M. Pitts' *Well-Scoped Locally Nameless* syntax —
generic over a Plotkin-style binding signature — together with its adequacy proof, a
Martin-Löf type theory development, decidability of βη-conversion for Gödel's
System T by normalization by evaluation, and the λ-/π-calculus examples.

Everything is checked by Lean **4.33.1** using **Lean core only**: no Mathlib, no
Batteries, no external dependencies.

## Provenance

The development follows Andrew M. Pitts, *Well-Scoped Locally Nameless Syntax*,
[arXiv:2605.08990](https://arxiv.org/abs/2605.08990).

> When using interactive theorem provers based on dependent type theory to define and
> reason about languages involving binding constructs, we advocate the use of a
> well-scoped version of the locally nameless method of representing syntax.

## Build

```sh
lake build
```

Builds five libraries (`WSLN`, `Adequacy`, `MLTT`, `GST`, `Examples`) in 56 jobs. A
cold build takes a couple of minutes; `MLTT.Substitution` dominates by a wide margin.

## Layout

| Path | Contents |
| --- | --- |
| `WSLN/` | The core library: scopes, atoms, signatures, terms, substitution, opening/closing |
| `Adequacy/` | Nameful syntax and the bijection with locally closed WSLN terms |
| `MLTT/` | Martin-Löf type theory in WSLN style, and its metatheory |
| `GST/` | Gödel's System T: normalization by evaluation and decidable βη-conversion |
| `Examples/` | Untyped λ-calculus, π-calculus, adequacy and System T at concrete signatures |

Each directory has a root facade module (`WSLN.lean`, `Adequacy.lean`, …) that imports
its parts in dependency order.

### `WSLN/`

| Module | Contents |
| --- | --- |
| `Prelude` | The few prelude items with no ergonomic Lean-core counterpart |
| `Index` | Scopes as `Nat`, de Bruijn indices as `Fin n`, scoped sets and weakening |
| `Atom` | `Atom := Nat`, the inductive `Fset` of finite atom sets, membership |
| `Fresh` | Finite support, freshness `x # a`, and the `fresh` operation |
| `Sig` | `Sig`: a type of operators plus an arity `Op → List Nat` |
| `Term` | `Trm Sg n` and `Arg Sg n ms`, with decidable equality |
| `Substitution` | `Sb Sg := Atom → Trm Sg 0`, `Rn := Atom → Atom`, the action `σ * t` |
| `Concretion` | `opn`, and concretion `t[u]` / `t[x]` via `GetElem` |
| `Abstraction` | `cls`, and abstraction `x ． t` |
| `Size` | `Trm.size`, for recursion on locally closed terms |

The central family is

```lean
inductive Trm (Sg : Sig) : Nat → Type where
```

with `Trm.var` for scoped de Bruijn indices (`Fin n`), `Trm.atom` for free names, and
`Trm.op` for compound terms. A term is *locally closed* when `n = 0`; those are the
terms in bijection with conventional syntax modulo α-equivalence.

### `Adequacy/`

`Adequacy/Nameful.lean` defines conventional named syntax (`NomTrm`, `NomArg`,
`NomBnd`) and α-equivalence `~`. `Adequacy/Translation.lean` defines the translation
`toWS` and its inverse `toNom`, and proves the bijection:

```lean
theorem injective  {Sg : Sig} (M N : NomTrm Sg) (e : toWS M = toWS N) : M ~ N
theorem bijection  {Sg : Sig} (t : Trm Sg 0)   : toWS (toNom t) = t
theorem bijection₂ {Sg : Sig} (M : NomTrm Sg)  : toNom (toWS M) ~ M
```

`Adequacy/Substitution.lean` shows the bijection carries capture-avoiding nameful
substitution to the WSLN substitution action (`mulCorrect`, `updateCorrect`).

`toNom` is defined by well-founded recursion on `Trm.size`, so the kernel cannot
reduce it; `Examples/Adequacy.lean` therefore checks the round trip with `#guard`
(compiler evaluation) alongside the theorem-backed `rfl` checks.

### `MLTT/`

Martin-Löf type theory with countably many non-cumulative universes, Π-types, `Nat`,
and intensional identity types, presented with **cofinitely quantified** binding
rules.

| Module | Contents |
| --- | --- |
| `Syntax` | The signature, pattern constructors (`𝚷`, `𝛌`, `𝐈𝐝`, `𝐍𝐚𝐭`, …), contexts |
| `Judgement` | The four judgement forms, packed as `Jg`; support and substitution on them |
| `Cofinite` | `Ok` and `Deriv` (mutual), context conversion, weakening, substitution typing |
| `Ok` | Provable judgements have well-formed contexts |
| `WellScoped` | Derivations only mention names in the context (`derivSupp`) |
| `Weakening` | `wkDeriv` |
| `Substitution` | `sbDeriv`, `eqSbTm` — two exhaustive inductions over the thirty `Deriv` rules |
| `Admissible` | Context conversion, concretion lemmas, derived rules |
| `ExistsFresh` | The "choose one fresh atom" variants of the cofinite rules |
| `Uniqueness` | `svTy`: types are unique up to conversion, and levels are unique |

```lean
theorem svTy {l l' : Lvl} {Γ : Cx} {A A' : Ty0} {a : Tm0}
    (q : Γ ⊢ a ∶ A ⦂ l) (q' : Γ ⊢ a ∶ A' ⦂ l') : (l = l') ∧ (Γ ⊢ A ＝ A' ⦂ l)
```

### `GST/`

Gödel's System T — simply typed λ-calculus with `𝐍𝐚𝐭` and `𝐧𝐫𝐞𝐜` — with its
βη-conversion relation shown decidable by **normalization by evaluation**: terms are
interpreted in presheaves over the category of typed renamings, and the normal form
is read back off the interpretation.  The binding rules are *exists-fresh* (one atom
plus two freshness side conditions), not cofinite.

| Module | Contents |
| --- | --- |
| `Syntax` | Simple types, the signature, pattern constructors (`𝛌`, `∙`, `𝐳𝐞𝐫𝐨`, `𝐬𝐮𝐜𝐜`, `𝐧𝐫𝐞𝐜`) |
| `Context` | `Cx`, indexed by its domain; `IsIn`, decidable lookup |
| `TypeSystem` | The typing and βη-conversion judgements, both `Type`-valued |
| `WellScoped` | Provable judgements only mention names in the context |
| `Setoid` | Bundled setoids, their morphisms, products and exponentials |
| `Renaming` | Typed renamings; renaming preserves typing and conversion |
| `Substitution` | Typed and convertible substitutions; `convTy₁`/`convTy₂` |
| `Admissible` | `lam'`, `betaLam'`, `lamInv` |
| `UniqueTypes` | `svVr`, `svTy`: types are unique |
| `NormalForm` | Mutual normal (`⊢ⁿ`) and neutral (`⊢ᵘ`) forms, and neutral substitutions |
| `Presheaf` | The category of renamings, presheaves on it, and its cartesian closed structure |
| `TypeSemantics` | The presheaves `Norm`/`Neut`, `𝓓` on types and `𝓔` on contexts |
| `ReifyReflect` | `reify`/`reflect` by recursion on the type; the initial environment |
| `TermSemantics` | `sem`: a derivation as a natural transformation, and its coherence laws |
| `LogicalRelation` | The glueing relation and the fundamental property `FP` |
| `Sound` | Convertible terms have equal interpretations |
| `Normalization` | `nf`, `NF1`, `NF2` |
| `DecidableConv` | `tyDec` and `convDec` |

```lean
def tyDec {S : Fset} (Γ : Cx S) (A : Ty) (a : Tm0) : Dec (Γ ⊢ a ∶ A)
def convDec {S : Fset} (Γ : Cx S) (A : Ty) (a a' : Tm0) : Dec (Γ ⊢ a ＝ a' ∶ A)
```

`Examples/GST.lean` runs both of them, and `nf`, on closed terms with `#guard`.

### `Examples/`

`Lambda.lean` and `PiCalc.lean` are the two example signatures from the paper. Both
end with `example`s that gate the build by forcing concretion, abstraction and
decidable equality to actually compute on concrete terms:

```lean
-- `beta` at a concrete redex: checks that `i0 [ 𝐚 3 ] = 𝐚 3` holds definitionally.
example : (𝛌 i0 ∙ (𝐯3 : Tm 0)) ⟶β (𝐯3 : Tm 0) := .beta i0 (𝐯3)
```

`Examples/Adequacy.lean` instantiates the adequacy theorems at `Lambda.sig` — they
are proved for an arbitrary signature, so they cannot be exercised inside `Adequacy/`
itself without importing a concrete one.  `Examples/GST.lean` builds a System T
typing derivation by hand and then runs `tyDec`, `convDec` and `nf` on closed terms.

## Notation

Scoped notation follows the paper. Open the namespace (`open WSLN`, `open MLTT`, …)
to bring it into scope.

| Lean | Meaning |
| --- | --- |
| `x # a` | `x` is fresh for `a`; also `x # y # a` and `x ## y` |
| `σ * t` | Action of a substitution or renaming on a term |
| `x ≔ u`, `σ ∘/ x ≔ u` | Single substitution, and update of a substitution |
| `t[u]`, `t[x]` | Concretion of a binder at a term or at a name |
| `x ． t` | Abstraction of the name `x` in `t` |
| `M ~ N` | α-equivalence of nameful terms |
| `Γ ⊢ J` | Derivability of the MLTT judgement `J` |
| `Γ ⨟ x ∶ A ⦂ l`, `◇` | Context extension and the empty context |
| `Γ ⊢ a ∶ A`, `Γ ⊢ a ＝ a' ∶ A` | Typing and βη-conversion in System T |
| `Γ ⨟ x ∶ A ∣ h`, `◇` | System T context extension (with its freshness proof) |

## License

Released into the public domain under
[CC0 1.0 Universal](https://creativecommons.org/publicdomain/zero/1.0/).

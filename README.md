# lean-wsln

A Lean 4 port of Andrew Pitts' Agda library **WSLN** — *Well-Scoped Locally Nameless*
syntax, generic over a Plotkin-style binding signature — together with its adequacy
proof, a Martin-Löf type theory development, and the λ-/π-calculus examples.

Everything is checked by Lean **4.33.1** using **Lean core only**: no Mathlib, no
Batteries, no external dependencies.

## Provenance

This is a port, not new mathematics. All statements and proof structure follow the
Agda originals; each Lean declaration carries an `Agda:` traceability comment naming
its counterpart.

- **Agda library** — [amp12/WSLN](https://github.com/amp12/WSLN),
  browsable at <https://amp12.github.io/WSLN/#githubcomamp12wsln>
  (checked with Agda 2.8.0 under `--safe --without-K`).
- **Paper** — Andrew M. Pitts, *Well-Scoped Locally Nameless Syntax*,
  [arXiv:2605.08990](https://arxiv.org/abs/2605.08990).

> When using interactive theorem provers based on dependent type theory to define and
> reason about languages involving binding constructs, we advocate the use of a
> well-scoped version of the locally nameless method of representing syntax.

## Build

```sh
lake build
```

Builds four libraries (`WSLN`, `Adequacy`, `MLTT`, `Examples`) in 35 jobs. A cold
build takes a few minutes; `MLTT.Substitution` and `MLTT.Admissible` dominate, and
seven proofs raise `maxHeartbeats` to `1000000` in a scoped `set_option ... in`.

The build is self-checking. `MLTT/Uniqueness.lean` ends with `#print axioms` for the
seven headline metatheorems; `Adequacy/Translation.lean` does the same for
`bijection`. All report `[propext, Quot.sound]` — no `sorryAx`, no added axiom. There
is no `sorry`, `admit`, or `native_decide` anywhere in the source.

The reference Agda sources cited throughout the docstrings as `agda-code/agda/...`
are not vendored here. To follow along:

```sh
git clone https://github.com/amp12/WSLN agda-code
```

## Layout

| Path | Contents |
| --- | --- |
| `WSLN/` | The core library: scopes, atoms, signatures, terms, substitution, opening/closing |
| `Adequacy/` | Nameful syntax and the bijection with locally closed WSLN terms |
| `MLTT/` | Martin-Löf type theory in WSLN style, and its metatheory |
| `Examples/` | Untyped λ-calculus, π-calculus, and adequacy instantiated at a concrete signature |

Each directory has a root facade module (`WSLN.lean`, `Adequacy.lean`, …) that imports
its parts in dependency order.

### `WSLN/`

| Module | Agda source | Contents |
| --- | --- | --- |
| `Prelude` | `Prelude/*` | The few prelude items with no ergonomic Lean-core counterpart |
| `Index` | `WSLN/Index` | Scopes as `Nat`, de Bruijn indices as `Fin n`, scoped sets and weakening |
| `Atom` | `WSLN/Atom` | `Atom := Nat`, the inductive `Fset` of finite atom sets, membership |
| `Fresh` | `WSLN/Fresh` | Finite support, freshness `x # a`, and the `fresh` operation |
| `Sig` | `WSLN/Sig/Sig` | `Sig`: a type of operators plus an arity `Op → List Nat` |
| `Term` | `WSLN/Sig/Term` | `Trm Sg n` and `Arg Sg n ms`, with decidable equality |
| `Substitution` | `WSLN/Sig/Substitution` | `Sb Sg := Atom → Trm Sg 0`, `Rn := Atom → Atom`, the action `σ * t` |
| `Concretion` | `WSLN/Sig/Concretion` | `opn`, and concretion `t[u]` / `t[x]` via `GetElem` |
| `Abstraction` | `WSLN/Sig/Abstraction` | `cls`, and abstraction `x ． t` |
| `Size` | `WSLN/Sig/Size` | `Trm.size`, for recursion on locally closed terms |

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
itself without importing a concrete one.

## Notation

Scoped notation mirrors the Agda source, so proofs read the same in both languages.
Open the namespace (`open WSLN`, `open MLTT`, …) to bring it into scope.

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

## Port notes

The port is faithful to the Agda statements but idiomatic where Lean is stronger.

- **Proof irrelevance.** Agda's `isProp`/`isSet`/`hedberg` machinery, the inductive
  disequalities `_≠i_` / `_≠𝔸_`, and their irrelevance lemmas are all deleted: Lean's
  `Prop` is proof-irrelevant by definitional equality.
- **Signatures are explicit.** Agda passes `⦃ Σ : Sig ⦄` as an instance argument; the
  port takes an explicit `Sg`, so the λ-calculus, π-calculus and MLTT signatures
  coexist in one build without instance-coherence problems.
- **Pattern synonyms.** Agda's pattern synonyms become `@[match_pattern] def`s with
  ASCII names plus bold-unicode notation, so `Pi' l l' A B` and `𝚷 l l' A B` are
  interchangeable and both can be matched on.
- **Mutual induction.** Lean's `induction` tactic does not handle mutual inductives,
  so inductions over `Deriv` go through `Deriv.rec` with `motive_1 := fun _ _ => True`
  for the `Ok` half.
- **The equation trick.** `opn`/`cls` take the scope equation (`m = n + 1`) as an
  explicit argument rather than matching on it, because the recursive call under a
  binder of depth `k` needs `k + m = (k + n) + 1`.
- **Scope casts.** Core `Arg Sg n ms` stores a `Trm Sg (n + m)`, so at `n = 0` an
  arity-`m` argument has type `Trm Sg (0 + m)`, which does not reduce for a variable
  `m`. `Adequacy.Trm.castScope` is the single transport used for this, with a small
  simp set of interaction laws; there is deliberately no second convention.
- **No standard library.** Lean 4.33.1 core has no `Function.update`, no
  `Fin.succAbove`/`Fin.predAbove`, and its `Vector` is `Array`-backed, so the port
  keeps its own `updateFn`, `insert`/`remove`, and structural `Vec`.

## License

The Lean port follows the license of the upstream Agda library; see
[amp12/WSLN](https://github.com/amp12/WSLN) for the original terms and for the
authoritative source of every statement proved here.

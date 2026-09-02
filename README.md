# lean-wsln

A Lean 4 formalization of well-scoped locally nameless syntax — generic over a
Plotkin-style binding signature — following Andrew M. Pitts, *Well-Scoped Locally
Nameless Syntax*, [arXiv:2605.08990](https://arxiv.org/abs/2605.08990).

> When using interactive theorem provers based on dependent type theory to define and
> reason about languages involving binding constructs, we advocate the use of a
> well-scoped version of the locally nameless method of representing syntax.

Everything is checked by Lean **4.33.1** using **Lean core only**: no Mathlib, no
Batteries, no external dependencies.

## Build

```sh
lake build
```

Five libraries — `WSLN`, `Adequacy`, `MLTT`, `GST`, `Examples` — in 56 jobs. A cold
build takes a couple of minutes, dominated by `MLTT.Substitution`.

| Library | Contents |
| --- | --- |
| `WSLN/` | Scopes, atoms, signatures, terms, substitution, opening and closing |
| `Adequacy/` | Named syntax, and its bijection with locally closed terms |
| `MLTT/` | Martin-Löf type theory and its metatheory |
| `GST/` | Gödel's System T: normalization by evaluation, decidable conversion |
| `Examples/` | λ-calculus, π-calculus, and the above at concrete signatures |

Each has a facade module (`WSLN.lean`, `Adequacy.lean`, …) importing its parts in
dependency order.

## The representation

```lean
inductive Trm (Sg : Sig) : Nat → Type where
  | var {n : Nat} (i : Fin n) : Trm Sg n
  | atom {n : Nat} (x : Atom) : Trm Sg n
  | op {n : Nat} (o : Sg.Op) (ts : Arg Sg n (Sg.ar o)) : Trm Sg n
```

A *scope* is a natural number: how many de Bruijn indices are in scope. Bound
variables are indices (`Fin n`, so out-of-scope indices are unrepresentable), free
variables are atoms, and `Sg.ar : Op → List Nat` gives each operator's arity as the
number of names its arguments bind. A term is *locally closed* when `n = 0`; those
are the terms in bijection with conventional named syntax modulo α-equivalence.

## Results

**Adequacy** — named syntax is exactly the locally closed terms, up to α-equivalence:

```lean
theorem injective  {Sg : Sig} (M N : NomTrm Sg) (e : toWS M = toWS N) : M ~ N
theorem bijection  {Sg : Sig} (t : Trm Sg 0)   : toWS (toNom t) = t
theorem bijection₂ {Sg : Sig} (M : NomTrm Sg)  : toNom (toWS M) ~ M
```

The bijection carries capture-avoiding named substitution to the substitution action
on terms (`mulCorrect`, `updateCorrect`).

**MLTT** — types and levels are unique up to conversion:

```lean
theorem svTy {l l' : Lvl} {Γ : Cx} {A A' : Ty0} {a : Tm0} (q : Γ ⊢ a ∶ A ⦂ l)
    (q' : Γ ⊢ a ∶ A' ⦂ l') : (l = l') ∧ (Γ ⊢ A ＝ A' ⦂ l)
```

Countably many non-cumulative universes, Π-types, `Nat` and intensional identity
types, with **cofinitely quantified** binding rules. The metatheory is weakening
(`wkDeriv`), well-scopedness (`derivSupp`), substitution (`sbDeriv`, `eqSbTm` — two
exhaustive inductions over the thirty `Deriv` rules) and the admissible rules.

**GST** — βη-conversion for Gödel's System T is decidable:

```lean
def tyDec {S : Fset} (Γ : Cx S) (A : Ty) (a : Tm0) : Dec (Γ ⊢ a ∶ A)
def convDec {S : Fset} (Γ : Cx S) (A : Ty) (a a' : Tm0) : Dec (Γ ⊢ a ＝ a' ∶ A)
```

By normalization by evaluation: terms are interpreted in presheaves over the category
of typed renamings, and the normal form is read back off the interpretation (`nf`,
`NF1`, `NF2`). Binding rules here are *exists-fresh* rather than cofinite, and both
judgements are `Type`-valued, because the semantics eliminates a derivation into
data.

`Examples/` gates the build on all of this computing on concrete terms: concretion,
abstraction and decidable equality for the λ- and π-calculus signatures, and `tyDec`,
`convDec` and `nf` on closed System T terms.

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
| `M ~ N` | α-equivalence of named terms |
| `Γ ⊢ J` | Derivability of the MLTT judgement `J` |
| `Γ ⨟ x ∶ A ⦂ l`, `◇` | Context extension and the empty context |
| `Γ ⊢ a ∶ A`, `Γ ⊢ a ＝ a' ∶ A` | Typing and βη-conversion in System T |
| `Γ ⨟ x ∶ A ∣ h`, `◇` | System T context extension (with its freshness proof) |

## License

Released into the public domain under
[CC0 1.0 Universal](https://creativecommons.org/publicdomain/zero/1.0/).

import WSLN

/-!
# π-calculus

Port of `agda-code/agda/PiCalc.agda`: a well-scoped locally nameless
representation of π-calculus processes, structural congruence and reduction.
-/

namespace PiCalc

open WSLN

/-! ## Raw expressions -/

inductive Op where
  /-- Input prefixed process. -/
  | inp : Op
  /-- Output prefixed process. -/
  | out : Op
  /-- Parallel composition. -/
  | par : Op
  /-- Restriction. -/
  | nu : Op
  /-- Replication. -/
  | repl : Op
  /-- Termination. -/
  | null : Op
  deriving DecidableEq

def ar : Op → List Nat
  | .inp => [0, 1]
  | .out => [0, 0, 0]
  | .par => [0, 0]
  | .nu => [1]
  | .repl => [0]
  | .null => []

def sig : Sig := ⟨Op, ar⟩

/-- π-calculus expressions in scope `n`. -/
abbrev Tm (n : Nat) := WSLN.Trm sig n

instance : DecidableEq sig.Op := inferInstanceAs (DecidableEq Op)

/-! ## Notation -/

@[match_pattern] def inP {n : Nat} (a : Atom) (P : Tm (n + 1)) : Tm n :=
  .op .inp (.cons (.atom a) (.cons P .nil))

@[match_pattern] def out {n : Nat} (a b : Atom) (P : Tm n) : Tm n :=
  .op .out (.cons (.atom a) (.cons (.atom b) (.cons P .nil)))

/-- Parallel composition. -/
@[match_pattern] def par {n : Nat} (P Q : Tm n) : Tm n :=
  .op .par (.cons P (.cons Q .nil))

/-- Name restriction. -/
@[match_pattern] def nu {n : Nat} (P : Tm (n + 1)) : Tm n := .op .nu (.cons P .nil)

/-- Replication. -/
@[match_pattern] def repl {n : Nat} (P : Tm n) : Tm n := .op .repl (.cons P .nil)

/-- The inert (null) process. -/
@[match_pattern] def O {n : Nat} : Tm n := .op .null .nil

-- Agda writes parallel composition `P ∥ Q`; `∣` is taken by Lean core's `Dvd`
-- notation, so the Lean port uses `∥`.
@[inherit_doc par] scoped infixl:68 " ∥ " => PiCalc.par
@[inherit_doc nu] scoped notation:max "ν " P:max => PiCalc.nu P
@[inherit_doc repl] scoped notation:max "‼ " P:max => PiCalc.repl P
@[inherit_doc O] scoped notation:max "𝐎" => PiCalc.O

/-! ## Well-formed processes -/

/-- Well-formed processes. -/
inductive Proc : Tm 0 → Prop where
  /-- Input prefixed process. -/
  | In {a x : Atom} {P : Tm 1} (q₀ : x # P) (q₁ : Proc (P[x])) : Proc (inP a P)
  /-- Output prefixed process. -/
  | Out {a b : Atom} {P : Tm 0} (q : Proc P) : Proc (out a b P)
  /-- Parallel composition. -/
  | Par {P Q : Tm 0} (q : Proc P) (q' : Proc Q) : Proc (P ∥ Q)
  /-- Channel restriction. -/
  | Nu {x : Atom} {P : Tm 1} (q₀ : x # P) (q₁ : Proc (P[x])) : Proc (ν P)
  /-- Process replication. -/
  | Repl {P : Tm 0} (q : Proc P) : Proc (‼ P)
  /-- Terminated process. -/
  | Null : Proc 𝐎

@[inherit_doc Proc] scoped notation:40 "⊢ " P:41 " proc" => PiCalc.Proc P

/-! ## Structural congruence -/

/-- Structural congruence. -/
inductive Cong : Tm 0 → Tm 0 → Prop where
  | Rfl {P : Tm 0} (q : ⊢ P proc) : Cong P P
  | Sym {P Q : Tm 0} (q : Cong P Q) : Cong Q P
  | Trs {P Q R : Tm 0} (q : Cong P Q) (q' : Cong Q R) : Cong P R
  | InCong {a x : Atom} {P P' : Tm 1} (q₀ : x # (P, P')) (q₁ : Cong (P[x]) (P'[x])) :
      Cong (inP a P) (inP a P')
  | OutCong {a b : Atom} {P P' : Tm 0} (q : Cong P P') : Cong (out a b P) (out a b P')
  | ParCong {P P' Q Q' : Tm 0} (q : Cong P P') (q' : Cong Q Q') :
      Cong (P ∥ Q) (P' ∥ Q')
  | NuCong {x : Atom} {P P' : Tm 1} (q₀ : x # (P, P')) (q₁ : Cong (P[x]) (P'[x])) :
      Cong (ν P) (ν P')
  | ReplCong {P P' : Tm 0} (q : Cong P P') : Cong (‼ P) (‼ P')
  | ParSym {P Q : Tm 0} (q : ⊢ P proc) (q' : ⊢ Q proc) : Cong (P ∥ Q) (Q ∥ P)
  | ParAssoc {P Q R : Tm 0} (q : ⊢ P proc) (q' : ⊢ Q proc) (q'' : ⊢ R proc) :
      Cong ((P ∥ Q) ∥ R) (P ∥ (Q ∥ R))
  | ParNull {P : Tm 0} (q : ⊢ P proc) : Cong (P ∥ 𝐎) P
  | nuSym {x y : Atom} {P : Tm 2} (q₀ : x # y # P) (q₁ : ⊢ P[x][y] proc) :
      Cong (ν (x ． ν (y ． P[x][y]))) (ν (y ． ν (x ． P[x][y])))
  | nuNull {x : Atom} : Cong (ν (x ． (𝐎 : Tm 0))) 𝐎
  | Extrude {x : Atom} {P : Tm 1} {Q : Tm 0} (q₀ : x # (P, Q)) (q₁ : ⊢ P[x] proc)
      (q₂ : ⊢ Q proc) : Cong (ν (x ． P[x] ∥ Q)) ((ν P) ∥ Q)
  | Repl {P : Tm 0} (q : ⊢ P proc) : Cong (‼ P) (P ∥ ‼ P)

@[inherit_doc Cong] scoped notation:40 "⊢ " P:41 " ＝ " Q:41 => PiCalc.Cong P Q

/-! ## Reduction -/

/-- Reduction of processes. -/
inductive Red : Tm 0 → Tm 0 → Prop where
  | Comm {a b x : Atom} {P : Tm 0} {Q : Tm 1} (q₀ : ⊢ P proc) (q₁ : x # Q)
      (q₂ : ⊢ Q[x] proc) : Red (out a b P ∥ inP a Q) (P ∥ Q[b])
  | Par {P Q R : Tm 0} (q : Red P Q) (q' : ⊢ R proc) : Red (P ∥ R) (Q ∥ R)
  | Nu {x : Atom} {P Q : Tm 1} (q₀ : x # (P, Q)) (q₁ : Red (P[x]) (Q[x])) :
      Red (ν P) (ν Q)
  | Struc {P P' Q Q' : Tm 0} (q : Red P Q) (q' : ⊢ P' ＝ P) (q'' : ⊢ Q ＝ Q') :
      Red P' Q'

@[inherit_doc Red] scoped notation:40 "⊢ " P:41 " ⟶ " Q:41 => PiCalc.Red P Q

/-! ## Checks

These `example`s gate the build: they exercise that concretion and abstraction
compute on concrete π-calculus expressions. -/

-- `νNull` on a concrete atom.
example : ⊢ ν ((5 : Atom) ． (𝐎 : Tm 0)) ＝ 𝐎 := .nuNull

-- A `Comm` reduction on concrete atoms; `(‼ 𝐎)[x]` must compute to `‼ 𝐎`.
example : ⊢ (out 1 2 𝐎 ∥ inP 1 (‼ (𝐎 : Tm 1))) ⟶ (𝐎 ∥ ‼ (𝐎 : Tm 0)) :=
  .Comm (x := 0) .Null (by decide) (.Repl .Null)

-- A well-formed input process, using `absConc` to build the binder.
example : ⊢ inP 1 ((3 : Atom) ． (‼ (𝐎 : Tm 0))) proc :=
  .In (x := 3) (fresh_abs 3 _) (by rw [concAbs']; exact .Repl .Null)

-- Replication unfolding, then a structural rewrite.
example : ⊢ ‼ (𝐎 : Tm 0) ＝ (𝐎 ∥ ‼ (𝐎 : Tm 0)) := .Repl .Null

end PiCalc
